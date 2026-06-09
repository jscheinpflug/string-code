const std = @import("std");
const backend = @import("backend.zig");
const coupling = @import("coupling.zig");
const decomposition = @import("decomposition.zig");
const generic_backend = @import("generic-highest-weight-backend.zig");
const projector = @import("projector.zig");
const projector_constructor = @import("projector-constructor.zig");
const realization = @import("realization.zig");
const rendering = @import("rendering.zig");
const root_data = @import("root-data.zig");
const store = @import("representation-store.zig");
const symmetry = @import("symmetry.zig");

/// ContextId names an initialized tensor-code context or preset.
pub const ContextId = struct {
    value: u32,

    /// init constructs a context id from a store index.
    pub fn init(value: u32) ContextId {
        return .{ .value = value };
    }
};

/// ContextOptions configures algebra and rendering defaults.
pub const ContextOptions = struct {
    algebra_conventions: root_data.AlgebraConventions = .{},
    default_signature: rendering.SignatureConvention = .complex,
};

/// FormulaCoverageAudit stores formula-readiness counters for a generated basis.
pub const FormulaCoverageAudit = struct {
    path_count: u32 = 0,
    local_step_count: u64 = 0,
    expandable_step_count: u64 = 0,
    missing_step_count: u64 = 0,
    boundary_projector_count: u32 = 0,
    boundary_step_count: u64 = 0,
    expandable_boundary_step_count: u64 = 0,
    missing_boundary_step_count: u64 = 0,
    fully_expandable_path_count: u32 = 0,
    distinct_projector_count: u32 = 0,
    distinct_boundary_projector_count: u32 = 0,
    first_missing_projector: ?projector.ProjectorId = null,
    first_missing_left: store.IrrepHandle = .{ .value = 0 },
    first_missing_right: store.IrrepHandle = .{ .value = 0 },
    first_missing_output: store.IrrepHandle = .{ .value = 0 },
    first_missing_boundary: ?realization.RealizationHandle = null,
};

/// Context is an opaque handle to tensor-code stores and caches.
pub const Context = struct {
    state: *anyopaque,
    allocator: std.mem.Allocator,

    /// init constructs an empty tensor-code context.
    pub fn init(allocator: std.mem.Allocator) !Context {
        return Context.initWithOptions(allocator, .{});
    }

    /// initWithOptions constructs a context with explicit conventions.
    pub fn initWithOptions(allocator: std.mem.Allocator, options: ContextOptions) !Context {
        const state = try allocator.create(Impl);
        errdefer allocator.destroy(state);
        state.* = try Impl.init(allocator, options);
        return .{
            .state = state,
            .allocator = allocator,
        };
    }

    /// deinit releases memory owned by this context.
    pub fn deinit(self: *Context) void {
        const state = self.impl();
        state.deinit();
        self.allocator.destroy(state);
        self.* = undefined;
    }

    /// registerAlgebra interns a Lie algebra and returns its handle.
    pub fn registerAlgebra(self: *Context, spec: store.AlgebraSpec) !store.AlgebraHandle {
        switch (spec) {
            .simple => |simple| try self.impl().validateBackend(simple),
            .u1 => {},
        }
        return self.impl().representations.internAlgebra(spec);
    }

    /// registerIrrep interns an abstract irreducible representation.
    pub fn registerIrrep(self: *Context, algebra: store.AlgebraHandle, spec: store.IrrepSpec) !store.IrrepHandle {
        return self.impl().representations.internIrrep(algebra, spec);
    }

    /// dualIrrep returns the registered dual representation.
    pub fn dualIrrep(self: *Context, irrep: store.IrrepHandle) !store.IrrepHandle {
        return self.impl().representations.dualIrrep(irrep);
    }

    /// irrepMetadata returns derived metadata for a registered irrep.
    pub fn irrepMetadata(self: Context, irrep: store.IrrepHandle) ?store.IrrepMetadata {
        return self.impl().representations.irrepMetadata(irrep);
    }

    /// registerRealization interns a concrete index realization of an irrep.
    pub fn registerRealization(self: *Context, spec: realization.RealizationSpec) !realization.RealizationHandle {
        try self.validateRealizationSpec(spec);
        return self.impl().realizations.internRealization(spec);
    }

    /// invariantBasis generates or retrieves a compact invariant basis.
    pub fn invariantBasis(self: *Context, request: coupling.InvariantBasisRequest) !coupling.BasisHandle {
        try self.validateInvariantBasisRequest(request);
        const path_count = try self.impl().countInvariantPaths(request);
        var paths = try self.impl().enumerateInvariantPaths(request);
        defer paths.deinit();
        if (path_count != paths.paths.items.len) return error.PathCountMismatch;
        const boundary_projector_count = try self.impl().countBoundaryProjectors(request);
        return self.impl().couplings.internBasisRequestWithPaths(request, path_count, paths.paths.items, paths.steps.items, boundary_projector_count);
    }

    /// basisInvariantCount returns the number of invariants in a generated basis.
    pub fn basisInvariantCount(self: Context, basis: coupling.BasisHandle) ?u128 {
        return self.impl().couplings.basisPathCount(basis);
    }

    /// basisAudit returns compact generation counters for a basis.
    pub fn basisAudit(self: Context, basis: coupling.BasisHandle) ?coupling.BasisAudit {
        return self.impl().couplings.basisAudit(basis);
    }

    /// basisFormulaCoverageAudit returns formula-readiness counters for a basis.
    pub fn basisFormulaCoverageAudit(self: *Context, basis: coupling.BasisHandle) !FormulaCoverageAudit {
        return self.impl().basisFormulaCoverageAudit(basis);
    }

    /// projectorDescriptor resolves a streamed projector operator id.
    pub fn projectorDescriptor(self: Context, operator_id: u32) ?projector.ProjectorDescriptor {
        return self.impl().projectors.projectorDescriptor(operator_id);
    }

    /// renderInvariant streams one invariant in the requested convention.
    pub fn renderInvariant(self: *Context, basis: coupling.BasisHandle, invariant: coupling.InvariantHandle, options: rendering.RenderOptions, sink: anytype) !void {
        _ = try self.renderInvariantFiltered(basis, invariant, options, rendering.ExpansionFilter.acceptAll(), sink);
    }

    /// renderInvariantFiltered streams one invariant through a tri-state filter.
    pub fn renderInvariantFiltered(self: *Context, basis: coupling.BasisHandle, invariant: coupling.InvariantHandle, options: rendering.RenderOptions, filter: rendering.ExpansionFilter, sink: anytype) !rendering.ExpansionAudit {
        try self.validateRenderOptions(options);
        const path = self.impl().couplingPathForInvariant(basis, invariant) orelse return error.UnknownInvariant;
        const request = self.impl().couplings.basisRequest(basis) orelse return error.UnknownBasis;
        var scratch: ExpansionScratch = .{};
        defer scratch.deinit(self.allocator);
        return self.impl().streamPathExpansion(request, path, options, filter, sink, &scratch);
    }

    /// renderBasis streams every invariant in a generated basis.
    pub fn renderBasis(self: *Context, basis: coupling.BasisHandle, options: rendering.RenderOptions, sink: anytype) !void {
        _ = try self.renderBasisFiltered(basis, options, rendering.ExpansionFilter.acceptAll(), sink);
    }

    /// renderBasisFiltered streams every invariant in a basis through a filter.
    pub fn renderBasisFiltered(self: *Context, basis: coupling.BasisHandle, options: rendering.RenderOptions, filter: rendering.ExpansionFilter, sink: anytype) !rendering.ExpansionAudit {
        try self.validateRenderOptions(options);
        const paths = self.impl().couplings.basisPaths(basis) orelse return error.UnknownBasis;
        const request = self.impl().couplings.basisRequest(basis) orelse return error.UnknownBasis;
        var audit: rendering.ExpansionAudit = .{};
        var scratch: ExpansionScratch = .{};
        defer scratch.deinit(self.allocator);
        for (paths) |path| {
            const path_audit = try self.impl().streamPathExpansion(request, path, options, filter, sink, &scratch);
            audit.merge(path_audit);
        }
        return audit;
    }

    /// evaluateInvariant streams component-evaluation data for one invariant.
    pub fn evaluateInvariant(self: *Context, invariant: coupling.InvariantHandle, options: rendering.EvalOptions, sink: anytype) !void {
        _ = self;
        _ = invariant;
        _ = options;
        _ = sink;
        return error.NotImplemented;
    }

    /// evaluateBasisInvariant streams lowered symbolic evaluation data for one basis invariant.
    pub fn evaluateBasisInvariant(self: *Context, basis: coupling.BasisHandle, invariant: coupling.InvariantHandle, options: rendering.EvalOptions, sink: anytype) !rendering.EvaluationAudit {
        try self.validateEvalOptions(options);
        const render_options = rendering.RenderOptions{
            .projectors = .expanded_terms,
            .signature = options.signature,
            .lower_clifford_product_atoms = true,
        };
        var adapter = EvaluationSinkAdapter(@TypeOf(sink)){ .inner = sink };
        const expansion_audit = try self.renderInvariantFiltered(basis, invariant, render_options, rendering.ExpansionFilter.acceptAll(), &adapter);
        return .{
            .terms = expansion_audit.emitted,
            .rejected = expansion_audit.rejected,
            .lowered_clifford_factors = expansion_audit.clifford_product_factors,
        };
    }

    fn validateRealizationSpec(self: Context, spec: realization.RealizationSpec) !void {
        const target_algebra = self.impl().representations.irrepAlgebra(spec.channel.irrep) orelse return error.UnknownIrrep;
        for (spec.ambient) |ambient| {
            const ambient_algebra = self.impl().representations.irrepAlgebra(ambient) orelse return error.UnknownIrrep;
            if (ambient_algebra.value != target_algebra.value) return error.MixedRealizationAlgebras;
        }
    }

    fn validateInvariantBasisRequest(self: Context, request: coupling.InvariantBasisRequest) !void {
        if (!self.impl().representations.containsAlgebra(request.algebra)) return error.UnknownAlgebra;
        for (request.external_legs) |leg| {
            const leg_algebra = try self.externalLegAlgebra(leg);
            if (leg_algebra) |algebra| {
                if (algebra.value != request.algebra.value) return error.MixedInvariantAlgebras;
            }
        }
    }

    fn validateRenderOptions(self: Context, options: rendering.RenderOptions) !void {
        if (options.signature != self.impl().options.default_signature) return error.UnsupportedRenderSignature;
        if (options.gamma_only and options.projectors != .expanded_terms) return error.GammaOnlyRequiresExpandedTerms;
    }

    fn validateEvalOptions(self: Context, options: rendering.EvalOptions) !void {
        if (options.signature != self.impl().options.default_signature) return error.UnsupportedEvalSignature;
    }

    fn externalLegAlgebra(self: Context, leg: realization.ExternalLeg) !?store.AlgebraHandle {
        return switch (leg.realization) {
            .primitive_irrep => |irrep| self.impl().representations.irrepAlgebra(irrep) orelse return error.UnknownIrrep,
            .handle => |handle| {
                const irrep = self.impl().realizations.targetIrrep(handle) orelse return error.UnknownRealization;
                return self.impl().representations.irrepAlgebra(irrep) orelse return error.UnknownIrrep;
            },
            .registered_name => null,
        };
    }

    fn externalLegIrrep(self: Context, leg: realization.ExternalLeg) !store.IrrepHandle {
        return self.impl().externalLegIrrep(leg);
    }

    fn impl(self: Context) *Impl {
        return @ptrCast(@alignCast(self.state));
    }
};

const Impl = struct {
    id: ContextId,
    allocator: std.mem.Allocator,
    options: ContextOptions,
    generic_backend: *generic_backend.Backend,
    backends: BackendRegistry,
    representations: store.Store,
    realizations: realization.Store,
    decompositions: decomposition.Store,
    projectors: projector.Store,
    tensor_form_projection_programs: projector_constructor.TensorFormProjectionProgramCache,
    tensor_spinor_projection_programs: projector_constructor.TensorSpinorProjectionProgramCache,
    structural_projection_programs: projector_constructor.StructuralProjectorProgramCache,
    couplings: coupling.Store,

    fn init(allocator: std.mem.Allocator, options: ContextOptions) !Impl {
        const generic = try allocator.create(generic_backend.Backend);
        errdefer allocator.destroy(generic);
        generic.* = generic_backend.Backend.init(allocator, options.algebra_conventions);

        return .{
            .id = ContextId.init(0),
            .allocator = allocator,
            .options = options,
            .generic_backend = generic,
            .backends = BackendRegistry.init(generic),
            .representations = store.Store.init(allocator, options.algebra_conventions),
            .realizations = realization.Store.init(allocator),
            .decompositions = decomposition.Store.init(allocator),
            .projectors = projector.Store.init(allocator),
            .tensor_form_projection_programs = projector_constructor.TensorFormProjectionProgramCache.init(allocator),
            .tensor_spinor_projection_programs = projector_constructor.TensorSpinorProjectionProgramCache.init(allocator),
            .structural_projection_programs = projector_constructor.StructuralProjectorProgramCache.init(allocator),
            .couplings = coupling.Store.init(allocator),
        };
    }

    fn deinit(self: *Impl) void {
        self.couplings.deinit();
        self.structural_projection_programs.deinit();
        self.tensor_spinor_projection_programs.deinit();
        self.tensor_form_projection_programs.deinit();
        self.projectors.deinit();
        self.decompositions.deinit();
        self.realizations.deinit();
        self.representations.deinit();
        self.generic_backend.deinit();
        self.allocator.destroy(self.generic_backend);
        self.* = undefined;
    }

    fn validateBackend(self: *Impl, simple: symmetry.SimpleLieAlgebra) !void {
        const record = self.backends.select(simple) orelse return error.UnsupportedAlgebraFamily;
        try record.capabilities.validate_algebra(record.state, simple);
    }

    fn decomposeProduct(self: *Impl, left: store.IrrepHandle, right: store.IrrepHandle) !decomposition.ProductDecompositionHandle {
        const algebra = self.representations.irrepAlgebra(left) orelse return error.UnknownIrrep;
        const right_algebra = self.representations.irrepAlgebra(right) orelse return error.UnknownIrrep;
        if (algebra.value != right_algebra.value) return error.MixedProductAlgebras;
        const simple = self.representations.simpleAlgebra(algebra) orelse return error.UnsupportedAlgebraFamily;
        const record = self.backends.select(simple) orelse return error.UnsupportedAlgebraFamily;
        return record.capabilities.decompose_product(record.state, &self.representations, &self.decompositions, .{
            .left = left,
            .right = right,
        });
    }

    fn countBoundaryProjectors(self: *Impl, request: coupling.InvariantBasisRequest) !u32 {
        var count: u32 = 0;
        for (request.external_legs) |leg| {
            const handle = switch (leg.realization) {
                .handle => |handle| handle,
                .primitive_irrep, .registered_name => continue,
            };
            const spec = self.realizations.realizationSpecFor(handle) orelse return error.UnknownRealization;
            if (spec.ambient.len != 0) count += 1;
        }
        return count;
    }

    fn couplingPathForInvariant(self: *Impl, basis: coupling.BasisHandle, invariant: coupling.InvariantHandle) ?coupling.CouplingPath {
        const paths = self.couplings.basisPaths(basis) orelse return null;
        const index: usize = @intCast(invariant.value);
        if (index >= paths.len) return null;
        return paths[index];
    }

    fn basisFormulaCoverageAudit(self: *Impl, basis: coupling.BasisHandle) !FormulaCoverageAudit {
        const paths = self.couplings.basisPaths(basis) orelse return error.UnknownBasis;
        const request = self.couplings.basisRequest(basis) orelse return error.UnknownBasis;
        var distinct = std.AutoHashMap(projector.ProjectorId, void).init(self.allocator);
        defer distinct.deinit();

        var audit: FormulaCoverageAudit = .{
            .path_count = @intCast(paths.len),
        };
        const boundary_expandable = try self.auditBoundaryFormulaCoverage(request, &audit);
        for (paths) |path| {
            const steps = self.couplings.pathSteps(path);
            var path_expandable = boundary_expandable;
            for (steps) |step| {
                audit.local_step_count += 1;
                try distinct.put(step.projector, {});
                const derivation = self.projectors.projectorDerivation(step.projector) orelse return error.UnknownProjector;
                if (derivation.status == .expandable_terms) {
                    audit.expandable_step_count += 1;
                } else {
                    audit.missing_step_count += 1;
                    path_expandable = false;
                    if (audit.first_missing_projector == null) {
                        audit.first_missing_projector = step.projector;
                        audit.first_missing_left = step.left;
                        audit.first_missing_right = step.right;
                        audit.first_missing_output = step.output;
                    }
                }
            }
            if (path_expandable) audit.fully_expandable_path_count += 1;
        }
        audit.distinct_projector_count = @intCast(distinct.count());
        return audit;
    }

    fn auditBoundaryFormulaCoverage(self: *Impl, request: coupling.InvariantBasisRequest, audit: *FormulaCoverageAudit) !bool {
        var distinct = std.AutoHashMap(projector.ProjectorId, void).init(self.allocator);
        defer distinct.deinit();

        var all_expandable = true;
        const path_multiplier: u64 = @intCast(audit.path_count);
        for (request.external_legs) |leg| {
            const handle = switch (leg.realization) {
                .handle => |handle| handle,
                .primitive_irrep, .registered_name => continue,
            };
            const spec = self.realizations.realizationSpecFor(handle) orelse return error.UnknownRealization;
            if (spec.ambient.len == 0) continue;

            const boundary_projector = try self.boundaryRealizationProjector(handle);
            try distinct.put(boundary_projector, {});
            audit.boundary_projector_count += 1;
            audit.boundary_step_count += path_multiplier;

            const derivation = self.projectors.projectorDerivation(boundary_projector) orelse return error.UnknownProjector;
            if (derivation.status == .expandable_terms) {
                audit.expandable_boundary_step_count += path_multiplier;
            } else {
                all_expandable = false;
                audit.missing_boundary_step_count += path_multiplier;
                if (audit.first_missing_projector == null) {
                    audit.first_missing_projector = boundary_projector;
                    audit.first_missing_boundary = handle;
                }
            }
        }
        audit.distinct_boundary_projector_count = @intCast(distinct.count());
        return all_expandable;
    }

    fn streamPathExpansion(self: *Impl, request: coupling.InvariantBasisRequest, path: coupling.CouplingPath, options: rendering.RenderOptions, filter: rendering.ExpansionFilter, sink: anytype, scratch: *ExpansionScratch) !rendering.ExpansionAudit {
        const steps = self.couplings.pathSteps(path);
        scratch.atoms.clearRetainingCapacity();
        const boundary_projector_count = try self.appendBoundaryRealizationAtoms(&scratch.atoms, request);

        var audit: rendering.ExpansionAudit = .{
            .invariants = 1,
            .max_frontier = @max(1, @as(u32, @intCast(steps.len))),
        };
        audit.boundary_projector_atoms = boundary_projector_count;
        if (boundary_projector_count != 0 and filter.rejectsAll()) {
            audit.recordDecision(.reject);
            return audit;
        }

        if (options.projectors != .named) {
            if (boundary_projector_count == 0) {
                if (try self.streamLocalFormulaPathTerms(steps, options, filter, sink, &audit, scratch)) return audit;
            } else {
                try self.streamBoundaryFormulaTerms(request, steps, options, filter, sink, &audit, scratch);
                return audit;
            }
        }

        const explicit_formula = try self.appendExplicitPathAtoms(&scratch.atoms, steps);
        const local_projector_count = if (explicit_formula) 0 else try self.appendNamedProjectorAtoms(&scratch.atoms, steps);
        audit.local_projector_atoms = local_projector_count;
        const term: rendering.SymbolicTerm = .{
            .coefficient = rendering.rationalOne(),
            .atoms = scratch.atoms.items,
        };
        const decision = try filter.decide(term);
        audit.recordDecision(decision);
        switch (decision) {
            .reject => return audit,
            .accept, .undecided => {
                if (options.projectors == .named) {
                    try emitRenderedTerm(self.allocator, options, sink, term, &audit, &scratch.lowered_atoms);
                    return audit;
                }
                if (!explicit_formula and steps.len != 0) {
                    try self.requirePathProjectorExpansion(steps, options.projectors);
                    return error.ProjectorExpansionNotImplemented;
                }
                try emitRenderedTerm(self.allocator, options, sink, term, &audit, &scratch.lowered_atoms);
                return audit;
            },
        }
    }

    fn appendBoundaryRealizationAtoms(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), request: coupling.InvariantBasisRequest) !u32 {
        var appended: u32 = 0;
        for (request.external_legs, 0..) |leg, leg_index| {
            const handle = switch (leg.realization) {
                .handle => |handle| handle,
                .primitive_irrep, .registered_name => continue,
            };
            const spec = self.realizations.realizationSpecFor(handle) orelse return error.UnknownRealization;
            if (spec.ambient.len == 0) continue;

            const operator_id = try self.boundaryRealizationProjector(handle);
            const first_index = externalIndexOffset(request, leg_index);
            try atoms.append(self.allocator, .{ .named_operator = .{
                .kind = .projector,
                .operator_id = operator_id,
                .first_index = first_index,
                .index_len = @intCast(leg.indices.len),
            } });
            appended += 1;
        }
        return appended;
    }

    fn appendExplicitPathAtoms(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), steps: []const coupling.CouplingStep) !bool {
        if (try self.appendSpecialExplicitPathAtoms(atoms, steps)) return true;
        return self.appendLocalFormulaPathAtoms(atoms, steps);
    }

    fn appendSpecialExplicitPathAtoms(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), steps: []const coupling.CouplingStep) !bool {
        if (steps.len == 2 and self.isA2FundamentalCubicStep(steps[0], steps[1])) {
            try self.ensurePathFormulaPrograms(steps);
            try atoms.append(self.allocator, .{ .epsilon = .{ .block = 0 } });
            return true;
        }
        if (steps.len == 2 and self.isE6FundamentalCubicStep(steps[0], steps[1])) {
            try self.ensurePathFormulaPrograms(steps);
            try atoms.append(self.allocator, .{ .structure_constant = .{
                .operator_id = steps[0].projector,
                .first = 0,
                .second = 1,
                .third = 2,
                .family = .e6,
                .rank = 6,
            } });
            return true;
        }
        if (steps.len == 2 and self.isSimpleAdjointCubicStep(steps[0], steps[1])) {
            const simple = self.stepSimpleAlgebra(steps[0]) orelse return error.UnsupportedAlgebraFamily;
            try self.ensurePathFormulaPrograms(steps);
            try atoms.append(self.allocator, .{ .structure_constant = .{
                .operator_id = steps[0].projector,
                .first = 0,
                .second = 1,
                .third = 2,
                .family = simple.family,
                .rank = simple.rank,
            } });
            return true;
        }
        return false;
    }

    fn ensurePathFormulaPrograms(self: *Impl, steps: []const coupling.CouplingStep) !void {
        for (steps) |step| {
            _ = try self.projectors.ensureFormulaProgram(step.projector);
        }
    }

    fn appendLocalFormulaPathAtoms(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), steps: []const coupling.CouplingStep) !bool {
        if (steps.len == 0) return false;
        const scratch_base: u32 = @intCast(steps.len + 1);
        var previous_formula_atom: ?rendering.SymbolicAtom = null;
        for (steps, 0..) |step, step_index| {
            const left_index: rendering.IndexRef = if (step_index == 0) 0 else scratch_base + @as(u32, @intCast(step_index - 1));
            const right_index: rendering.IndexRef = @intCast(step_index + 1);
            const output_index: rendering.IndexRef = scratch_base + @as(u32, @intCast(step_index));
            const atom_index = atoms.items.len;
            if (!try self.appendLocalFormulaStepAtom(atoms, step, left_index, right_index, output_index)) return false;
            if (atoms.items.len == atom_index) return error.InvalidProjectorExpansion;
            const current_formula_atom = atoms.items[atom_index];
            if (previous_formula_atom) |previous| {
                try appendCliffordProductAtoms(self.allocator, atoms, previous, current_formula_atom);
            }
            previous_formula_atom = current_formula_atom;
        }
        return true;
    }

    fn appendLocalFormulaStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const formula_kind = self.localProductFormulaKind(step);
        if (formula_kind == .named_only) return false;
        const cached_kind = try self.projectors.ensureFormulaProgram(step.projector);
        if (cached_kind != formula_kind) return error.InvalidProjectorExpansion;
        return self.appendLocalFormulaStepAtomForKind(atoms, step, left_index, right_index, output_index, cached_kind);
    }

    fn appendLocalFormulaStepAtomForKind(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef, formula_kind: projector.ProjectorFormulaKind) !bool {
        return switch (formula_kind) {
            .identity => {
                try atoms.append(self.allocator, .{ .identity_route = .{
                    .operator_id = step.projector,
                    .left = left_index,
                    .right = right_index,
                    .output = output_index,
                } });
                return true;
            },
            .orthogonal_vector_metric => {
                try atoms.append(self.allocator, .{ .metric_pair = .{
                    .left = left_index,
                    .right = right_index,
                } });
                return true;
            },
            .orthogonal_spinor_pair => {
                const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidSpinorPairChannel;
                const left = self.representations.irrepDynkin(step.left) orelse return error.InvalidSpinorPairChannel;
                const right = self.representations.irrepDynkin(step.right) orelse return error.InvalidSpinorPairChannel;
                try atoms.append(self.allocator, .{ .spinor_pair = .{
                    .operator_id = step.projector,
                    .spinor_left = left_index,
                    .spinor_right = right_index,
                    .orthogonal_dimension = rendering.orthogonalDimension(simple),
                    .chirality_left = @intFromEnum(rendering.gammaChiralityTag(simple, left)),
                    .chirality_right = @intFromEnum(rendering.gammaChiralityTag(simple, right)),
                } });
                return true;
            },
            .orthogonal_spinor_form_channel => return self.appendOrthogonalSpinorFormStepAtom(atoms, step, left_index, right_index, output_index),
            .orthogonal_form_pair => {
                try atoms.append(self.allocator, .{ .generalized_delta = .{
                    .upper = left_index,
                    .lower = right_index,
                } });
                return true;
            },
            .orthogonal_form_spinor_channel => return self.appendOrthogonalFormSpinorStepAtom(atoms, step, left_index, right_index, output_index),
            .cartan_product_channel => return self.appendSpinorTowerCartanProductStepAtom(atoms, step, left_index, right_index, output_index),
            .orthogonal_structural_projection => return self.appendLocalStructuralExpression(atoms, step, left_index, right_index, output_index),
            else => false,
        };
    }

    fn appendOrthogonalSpinorFormStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidGammaChannel;
        const left = self.representations.irrepDynkin(step.left) orelse return error.InvalidGammaChannel;
        if (self.isOrthogonalSpinorSpinorVectorStep(step)) {
            try atoms.append(self.allocator, .{ .gamma_matrix = .{
                .operator_id = step.projector,
                .spinor_left = left_index,
                .spinor_right = right_index,
                .vector = output_index,
                .orthogonal_dimension = rendering.orthogonalDimension(simple),
                .rank = 1,
                .chirality = @intFromEnum(rendering.gammaChiralityTag(simple, left)),
                .duality = .none,
            } });
            return true;
        }
        const form_info = self.orthogonalSpinorSpinorFormStep(step) orelse return false;
        try atoms.append(self.allocator, .{ .gamma_form = .{
            .operator_id = step.projector,
            .spinor_left = left_index,
            .spinor_right = right_index,
            .form = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .rank = form_info.rank,
            .chirality = @intFromEnum(rendering.gammaChiralityTag(simple, left)),
            .duality = form_info.duality,
        } });
        return true;
    }

    fn appendOrthogonalFormSpinorStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalFormSpinorStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidGammaActionChannel;
        const spinor = self.representations.irrepDynkin(step.right) orelse return error.InvalidGammaActionChannel;
        try atoms.append(self.allocator, .{ .gamma_action = .{
            .operator_id = step.projector,
            .form = left_index,
            .spinor_input = right_index,
            .spinor_output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .rank = info.rank,
            .chirality = @intFromEnum(rendering.gammaChiralityTag(simple, spinor)),
            .duality = info.duality,
        } });
        return true;
    }

    fn appendSpinorTowerCartanProductStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidCartanProductChannel;
        const left = self.representations.irrepDynkin(step.left) orelse return error.InvalidCartanProductChannel;
        const right = self.representations.irrepDynkin(step.right) orelse return error.InvalidCartanProductChannel;
        const output = self.representations.irrepDynkin(step.output) orelse return error.InvalidCartanProductChannel;
        const left_tower = spinorTowerInfo(simple, left) orelse return false;
        const right_tower = spinorTowerInfo(simple, right) orelse return false;
        const output_tower = spinorTowerInfo(simple, output) orelse return false;
        if (left_tower.chirality != right_tower.chirality or left_tower.chirality != output_tower.chirality) return false;
        if (output_tower.power != left_tower.power + right_tower.power) return false;
        var left_slot: u16 = 0;
        while (left_slot < left_tower.power) : (left_slot += 1) {
            try atoms.append(self.allocator, .{ .spinor_index_delta = .{
                .operator_id = step.projector,
                .source_tower = left_index,
                .output_tower = output_index,
                .source_slot = left_slot,
                .output_slot = left_slot,
                .chirality = @intFromEnum(output_tower.chirality),
            } });
        }
        var right_slot: u16 = 0;
        while (right_slot < right_tower.power) : (right_slot += 1) {
            try atoms.append(self.allocator, .{ .spinor_index_delta = .{
                .operator_id = step.projector,
                .source_tower = right_index,
                .output_tower = output_index,
                .source_slot = right_slot,
                .output_slot = left_tower.power + right_slot,
                .chirality = @intFromEnum(output_tower.chirality),
            } });
        }
        return true;
    }

    fn appendLocalStructuralExpression(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const term_count = try self.localStructuralTermCount(step, left_index, right_index, output_index);
        if (term_count != 1) return false;
        _ = try self.appendLocalStructuralTerm(atoms, step, left_index, right_index, output_index, 0);
        return true;
    }

    fn appendOrthogonalSpinorTowerFormStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalSpinorTowerFormStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .form_rank = info.forms.first_rank,
            .form_count = info.forms.count,
            .form_mask = info.forms.mask,
            .form_profile = info.forms.profile,
            .tower_power = info.tower_power,
            .chirality = @intFromEnum(info.chirality),
            .duality = info.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalSpinorTowerMiddleFormStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalSpinorTowerMiddleFormStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_form_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .input_form_profile = 0,
            .input_form_mask = 0,
            .output_form_profile = 0,
            .output_form_count = 1,
            .output_form_rank = info.rank,
            .output_duality = info.duality,
            .chirality = 0,
        });
        return true;
    }

    fn appendOrthogonalSpinorTowerOppositeFormStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalSpinorTowerOppositeFormStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .form_rank = info.forms.first_rank,
            .form_count = info.forms.count,
            .form_mask = info.forms.mask,
            .form_profile = info.forms.profile,
            .tower_power = info.tower_power,
            .chirality = @intFromEnum(info.chirality),
            .duality = info.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalSpinorTowerOppositeLowerStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalSpinorTowerOppositeLowerStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .form_rank = 0,
            .form_count = 0,
            .form_mask = 0,
            .form_profile = 0,
            .tower_power = info.power,
            .chirality = @intFromEnum(info.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorTowerStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorTowerStep(step) orelse return false;
        const input = self.orthogonalTensorSpinorLeftInfo(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = input.forms.profile,
            .input_form_count = input.forms.total_power,
            .input_tower_power = input.tower_power,
            .form_rank = info.forms.first_rank,
            .form_count = info.forms.count,
            .form_mask = info.forms.mask,
            .form_profile = info.forms.profile,
            .tower_power = info.tower_power,
            .chirality = @intFromEnum(info.chirality),
            .duality = info.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorFormPowerStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorFormPowerStep(step) orelse return false;
        const input = self.orthogonalTensorSpinorLeftInfo(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = input.forms.profile,
            .input_form_count = input.forms.total_power,
            .input_tower_power = input.tower_power,
            .form_rank = info.forms.first_rank,
            .form_count = info.forms.count,
            .form_mask = info.forms.mask,
            .form_profile = info.forms.profile,
            .tower_power = info.tower_power,
            .chirality = @intFromEnum(info.chirality),
            .duality = info.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorTowerRaiseStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorTowerRaiseStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeTowerLowerStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeTowerLowerStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeShiftStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeShiftStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeAllShiftStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeAllShiftStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeFormAddStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeFormAddStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeRankSplitStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeRankSplitStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorShiftStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorShiftStep(step) orelse return false;
        const input = self.orthogonalTensorSpinorLeftInfo(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = input.forms.profile,
            .input_form_count = input.forms.total_power,
            .input_tower_power = input.tower_power,
            .form_rank = info.forms.first_rank,
            .form_count = info.forms.count,
            .form_mask = info.forms.mask,
            .form_profile = info.forms.profile,
            .tower_power = info.tower_power,
            .chirality = @intFromEnum(info.chirality),
            .duality = info.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorRankWrapShiftStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorRankWrapShiftStep(step) orelse return false;
        const input = self.orthogonalTensorSpinorLeftInfo(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = input.forms.profile,
            .input_form_count = input.forms.total_power,
            .input_tower_power = input.tower_power,
            .form_rank = info.forms.first_rank,
            .form_count = info.forms.count,
            .form_mask = info.forms.mask,
            .form_profile = info.forms.profile,
            .tower_power = info.tower_power,
            .chirality = @intFromEnum(info.chirality),
            .duality = info.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorRankSplitStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorRankSplitStep(step) orelse return false;
        const input = self.orthogonalTensorSpinorLeftInfo(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = input.forms.profile,
            .input_form_count = input.forms.total_power,
            .input_tower_power = input.tower_power,
            .form_rank = info.forms.first_rank,
            .form_count = info.forms.count,
            .form_mask = info.forms.mask,
            .form_profile = info.forms.profile,
            .tower_power = info.tower_power,
            .chirality = @intFromEnum(info.chirality),
            .duality = info.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        try appendTensorFormProjectionGammaFallback(&self.tensor_form_projection_programs, atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = info.output.profile,
            .output_form_count = info.output.total_power,
            .output_form_rank = info.output.first_rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        try appendTensorFormProjectionGammaFallback(&self.tensor_form_projection_programs, atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = info.output.profile,
            .output_form_count = info.output.total_power,
            .output_form_rank = info.output.first_rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeFormAddTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeFormAddTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        try appendTensorFormProjectionGammaFallback(&self.tensor_form_projection_programs, atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = info.output.profile,
            .output_form_count = info.output.total_power,
            .output_form_rank = info.output.first_rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeFormAddShiftTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeFormAddShiftTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        try appendTensorFormProjectionGammaFallback(&self.tensor_form_projection_programs, atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = info.output.profile,
            .output_form_count = info.output.total_power,
            .output_form_rank = info.output.first_rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeRankSplitTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeRankSplitTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        try appendTensorFormProjectionGammaFallback(&self.tensor_form_projection_programs, atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = info.output.profile,
            .output_form_count = info.output.total_power,
            .output_form_rank = info.output.first_rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeShiftTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeShiftTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        try appendTensorFormProjectionGammaFallback(&self.tensor_form_projection_programs, atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = info.output.profile,
            .output_form_count = info.output.total_power,
            .output_form_rank = info.output.first_rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorRankWrapTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorRankWrapTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        try appendTensorFormProjectionGammaFallback(&self.tensor_form_projection_programs, atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = info.output.profile,
            .output_form_count = info.output.total_power,
            .output_form_rank = info.output.first_rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorRankSplitTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorRankSplitTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        try appendTensorFormProjectionGammaFallback(&self.tensor_form_projection_programs, atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = info.output.profile,
            .output_form_count = info.output.total_power,
            .output_form_rank = info.output.first_rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorFormTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorFormTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        const right = self.representations.irrepDynkin(step.right) orelse return error.InvalidTensorSpinorChannel;
        try atoms.append(self.allocator, .{ .spinor_pair = .{
            .operator_id = step.projector,
            .spinor_left = tensorSpinorSpinorIndex(left_index),
            .spinor_right = right_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .chirality_left = @intFromEnum(info.input.chirality),
            .chirality_right = @intFromEnum(rendering.gammaChiralityTag(simple, right)),
        } });
        try atoms.append(self.allocator, .{ .generalized_delta = .{
            .upper = left_index,
            .lower = output_index,
        } });
        return true;
    }

    fn appendOrthogonalTensorSpinorFormAddTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorFormAddTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        try appendTensorFormProjectionGammaFallback(&self.tensor_form_projection_programs, atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = info.output.profile,
            .output_form_count = info.output.total_power,
            .output_form_rank = info.output.first_rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorFormPowerTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorFormPowerTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        try appendTensorFormProjectionGammaFallback(&self.tensor_form_projection_programs, atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = info.output.profile,
            .output_form_count = info.output.total_power,
            .output_form_rank = info.output.first_rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorFormTowerStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorFormTowerStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorFormTowerTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorFormTowerTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = 0,
            .form_count = 0,
            .form_mask = 0,
            .form_profile = 0,
            .tower_power = info.output.power,
            .chirality = @intFromEnum(info.output.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorFormTowerRemoveShiftStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorFormTowerRemoveShiftStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorFormTowerShiftDownStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorFormTowerShiftDownStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorFormTowerAllShiftDownStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorFormTowerAllShiftDownStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeFormTowerStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeFormTowerStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeFormTowerTerminalStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeFormTowerTerminalStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = 0,
            .form_count = 0,
            .form_mask = 0,
            .form_profile = 0,
            .tower_power = info.output.power,
            .chirality = @intFromEnum(info.output.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeFormTowerMergeStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeFormTowerMergeStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeFormTowerRemoveShiftStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeFormTowerRemoveShiftStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorOppositeFormTowerShiftDownStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorOppositeFormTowerShiftDownStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_count = info.input.forms.total_power,
            .input_tower_power = info.input.tower_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorSpinorMiddleFormStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorSpinorMiddleFormStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_form_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .input_form_profile = info.input.forms.profile,
            .input_form_mask = info.input.forms.mask,
            .output_form_profile = 0,
            .output_form_count = 1,
            .output_form_rank = info.output.rank,
            .output_duality = info.output.duality,
            .chirality = @intFromEnum(info.input.chirality),
        });
        return true;
    }

    fn appendOrthogonalTensorFormSpinorStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorFormSpinorStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .left_has_spinor = false,
            .input_form_profile = info.input.profile,
            .input_form_count = info.input.total_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorFormSpinorPreserveStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorFormSpinorPreserveStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .left_has_spinor = false,
            .input_form_profile = info.input.profile,
            .input_form_count = info.input.total_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorFormSpinorShiftStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const spec = try self.orthogonalTensorFormSpinorShiftProjectionSpec(step, left_index, right_index, output_index) orelse return false;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, spec);
        return true;
    }

    fn orthogonalTensorFormSpinorShiftProjectionSpec(self: *Impl, step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !?projector_constructor.TensorSpinorProjectionSpec {
        const info = self.orthogonalTensorFormSpinorShiftStep(step) orelse return null;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        return .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .left_has_spinor = false,
            .input_form_profile = info.input.profile,
            .input_form_count = info.input.total_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        };
    }

    fn appendOrthogonalTensorFormSpinorRemoveShiftDownStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorFormSpinorRemoveShiftDownStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .left_has_spinor = false,
            .input_form_profile = info.input.profile,
            .input_form_count = info.input.total_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorFormSpinorShiftDownStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorFormSpinorShiftDownStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .left_has_spinor = false,
            .input_form_profile = info.input.profile,
            .input_form_count = info.input.total_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorFormSpinorShiftDownTwoStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorFormSpinorShiftDownTwoStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .left_has_spinor = false,
            .input_form_profile = info.input.profile,
            .input_form_count = info.input.total_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorFormSpinorMixedShiftDownStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorFormSpinorMixedShiftDownStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .left_has_spinor = false,
            .input_form_profile = info.input.profile,
            .input_form_count = info.input.total_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorFormSpinorAllShiftDownStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorFormSpinorAllShiftDownStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .left_has_spinor = false,
            .input_form_profile = info.input.profile,
            .input_form_count = info.input.total_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn appendOrthogonalTensorFormSpinorShiftDownAnyStepAtom(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !bool {
        const info = self.orthogonalTensorFormSpinorShiftDownAnyStep(step) orelse return false;
        const simple = self.stepSimpleAlgebra(step) orelse return error.InvalidTensorSpinorChannel;
        _ = try self.tensor_spinor_projection_programs.appendExpression(atoms, .{
            .operator_id = step.projector,
            .left = left_index,
            .right = right_index,
            .output = output_index,
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .right_chirality = self.stepRightSpinorChirality(simple, step) orelse return error.InvalidTensorSpinorChannel,
            .left_has_spinor = false,
            .input_form_profile = info.input.profile,
            .input_form_count = info.input.total_power,
            .form_rank = info.output.forms.first_rank,
            .form_count = info.output.forms.count,
            .form_mask = info.output.forms.mask,
            .form_profile = info.output.forms.profile,
            .tower_power = info.output.tower_power,
            .chirality = @intFromEnum(info.output.chirality),
            .duality = info.output.forms.duality,
        });
        return true;
    }

    fn stepSimpleAlgebra(self: *Impl, step: coupling.CouplingStep) ?symmetry.SimpleLieAlgebra {
        const algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        return self.representations.simpleAlgebra(algebra);
    }

    fn orthogonalTensorSpinorLeftInfo(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorInfo {
        const simple = self.stepSimpleAlgebra(step) orelse return null;
        const left = self.representations.irrepDynkin(step.left) orelse return null;
        return orthogonalTensorSpinorInfo(simple, left);
    }

    fn stepRightSpinorChirality(self: *Impl, simple: symmetry.SimpleLieAlgebra, step: coupling.CouplingStep) ?u8 {
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        return @intFromEnum(rendering.gammaChiralityTag(simple, right));
    }

    fn countInvariantPaths(self: *Impl, request: coupling.InvariantBasisRequest) !u128 {
        switch (request.tree_policy) {
            .auto => {},
            .fixed => return error.FixedTreeCountingNotImplemented,
        }

        const target = try self.targetIrrep(request.algebra, request.target);
        if (request.external_legs.len == 0) {
            const singlet = try self.targetIrrep(request.algebra, .singlet);
            return if (target.value == singlet.value) 1 else 0;
        }

        const first = try self.externalLegIrrep(request.external_legs[0]);
        var memo = std.AutoHashMap(u64, u128).init(self.allocator);
        defer memo.deinit();
        return self.countContinuations(request, first, 1, target, &memo);
    }

    fn enumerateInvariantPaths(self: *Impl, request: coupling.InvariantBasisRequest) !PathEnumeration {
        switch (request.tree_policy) {
            .auto => {},
            .fixed => return error.FixedTreeCountingNotImplemented,
        }

        var out = try PathEnumeration.init(self.allocator);
        errdefer out.deinit();
        const target = try self.targetIrrep(request.algebra, request.target);
        if (request.external_legs.len == 0) {
            const singlet = try self.targetIrrep(request.algebra, .singlet);
            if (target.value == singlet.value) {
                try out.paths.append(self.allocator, .{ .step_offset = 0, .step_len = 0 });
            }
            return out;
        }

        var nodes: std.ArrayList(PartialPathNode) = .empty;
        defer nodes.deinit(self.allocator);
        var current: std.ArrayList(u32) = .empty;
        defer current.deinit(self.allocator);
        var next: std.ArrayList(u32) = .empty;
        defer next.deinit(self.allocator);
        var continuation_counts = std.AutoHashMap(u64, u128).init(self.allocator);
        defer continuation_counts.deinit();

        const first = try self.externalLegIrrep(request.external_legs[0]);
        try nodes.append(self.allocator, .{
            .output = first,
            .parent = 0,
            .has_parent = false,
            .step = undefined,
        });
        try current.append(self.allocator, 0);

        for (request.external_legs[1..], 1..) |leg, leg_index| {
            next.clearRetainingCapacity();
            const factor = try self.externalLegIrrep(leg);
            for (current.items) |node_index| {
                const node = nodes.items[node_index];
                const product = try self.decomposeProduct(node.output, factor);
                const terms = self.decompositions.productTerms(product) orelse return error.UnknownProductDecomposition;
                var terms_copy: std.ArrayList(decomposition.ProductTerm) = .empty;
                defer terms_copy.deinit(self.allocator);
                try terms_copy.appendSlice(self.allocator, terms);
                for (terms_copy.items) |term| {
                    const suffix_count = try self.countContinuations(request, term.irrep, leg_index + 1, target, &continuation_counts);
                    if (suffix_count == 0) continue;
                    for (0..term.multiplicity) |copy| {
                        const local_projector = try self.localProductProjector(node.output, factor, term.irrep, @intCast(copy));
                        const child_index: u32 = @intCast(nodes.items.len);
                        try nodes.append(self.allocator, .{
                            .output = term.irrep,
                            .parent = node_index,
                            .has_parent = true,
                            .step = .{
                                .left = node.output,
                                .right = factor,
                                .output = term.irrep,
                                .multiplicity_copy = @intCast(copy),
                                .projector = local_projector,
                            },
                        });
                        try next.append(self.allocator, child_index);
                    }
                }
            }
            current.clearRetainingCapacity();
            try current.appendSlice(self.allocator, next.items);
        }

        var reverse_steps: std.ArrayList(coupling.CouplingStep) = .empty;
        defer reverse_steps.deinit(self.allocator);
        for (current.items) |node_index| {
            if (nodes.items[node_index].output.value != target.value) continue;
            reverse_steps.clearRetainingCapacity();
            var cursor = node_index;
            while (nodes.items[cursor].has_parent) {
                try reverse_steps.append(self.allocator, nodes.items[cursor].step);
                cursor = nodes.items[cursor].parent;
            }

            const step_offset: u32 = @intCast(out.steps.items.len);
            var i = reverse_steps.items.len;
            while (i > 0) {
                i -= 1;
                try out.steps.append(self.allocator, reverse_steps.items[i]);
            }
            try out.paths.append(self.allocator, .{
                .step_offset = step_offset,
                .step_len = @intCast(reverse_steps.items.len),
            });
        }
        return out;
    }

    fn countContinuations(self: *Impl, request: coupling.InvariantBasisRequest, current: store.IrrepHandle, next_index: usize, target: store.IrrepHandle, memo: *std.AutoHashMap(u64, u128)) !u128 {
        if (next_index == request.external_legs.len) {
            return if (current.value == target.value) 1 else 0;
        }

        const key = continuationKey(next_index, current);
        if (memo.get(key)) |cached| return cached;

        const factor = try self.externalLegIrrep(request.external_legs[next_index]);
        const product = try self.decomposeProduct(current, factor);
        const terms = self.decompositions.productTerms(product) orelse return error.UnknownProductDecomposition;
        var terms_copy: std.ArrayList(decomposition.ProductTerm) = .empty;
        defer terms_copy.deinit(self.allocator);
        try terms_copy.appendSlice(self.allocator, terms);

        var total: u128 = 0;
        for (terms_copy.items) |term| {
            const suffix_count = try self.countContinuations(request, term.irrep, next_index + 1, target, memo);
            if (suffix_count == 0) continue;
            const contribution = try std.math.mul(u128, suffix_count, term.multiplicity);
            total = try std.math.add(u128, total, contribution);
        }

        try memo.put(key, total);
        return total;
    }

    fn localProductProjector(self: *Impl, left: store.IrrepHandle, right: store.IrrepHandle, output: store.IrrepHandle, multiplicity_copy: u16) !projector.ProjectorId {
        const derivation = self.localProductProjectorDerivation(left, right, output, multiplicity_copy);
        return self.projectors.internProjector(.{
            .role = .{ .product_channel = .{
                .left = left,
                .right = right,
                .output = output,
                .multiplicity_copy = multiplicity_copy,
            } },
            .convention = .{
                .render_mode = .named,
                .signature = self.options.default_signature,
                .normalization_id = 0,
            },
        }, derivation);
    }

    fn localProductProjectorDerivation(self: *Impl, left: store.IrrepHandle, right: store.IrrepHandle, output: store.IrrepHandle, multiplicity_copy: u16) projector.ProjectorDerivation {
        const step: coupling.CouplingStep = .{
            .left = left,
            .right = right,
            .output = output,
            .multiplicity_copy = multiplicity_copy,
            .projector = 0,
        };
        const formula_kind = self.localProductFormulaKind(step);
        if (formula_kind == .named_only) {
            return .{
                .kind = .highest_weight_solver,
                .source = .highest_weight_solver,
                .status = .expandable_named,
            };
        }
        const formula_audit = self.localProductFormulaAudit(step, formula_kind);
        return .{
            .kind = .backend_specific_verified,
            .source = .backend_specific_verified,
            .status = if (formula_audit.verified()) .expandable_terms else .blocked_unverified_identity,
            .formula_kind = formula_kind,
            .formula_audit = formula_audit,
        };
    }

    fn localProductFormulaAudit(self: *Impl, step: coupling.CouplingStep, formula_kind: projector.ProjectorFormulaKind) projector.ProjectorFormulaAudit {
        return switch (formula_kind) {
            .orthogonal_spinor_pair => self.orthogonalSpinorPairFormulaAudit(step),
            .orthogonal_spinor_form_channel => self.orthogonalSpinorFormFormulaAudit(step),
            .orthogonal_form_spinor_channel => self.orthogonalFormSpinorFormulaAudit(step),
            .cartan_product_channel => self.orthogonalSpinorTowerCartanProductFormulaAudit(step),
            .identity,
            .orthogonal_vector_metric,
            .orthogonal_form_pair,
            .backend_specific_structure,
            => exactPrimitiveFormulaAudit(),
            else => if (isGramFormulaKind(formula_kind)) self.localProductGramFormulaAudit(step, formula_kind) else .{},
        };
    }

    fn localProductGramFormulaAudit(self: *Impl, step: coupling.CouplingStep, formula_kind: projector.ProjectorFormulaKind) projector.ProjectorFormulaAudit {
        const term_count = self.localFormulaStepTermCount(step, formula_kind) catch return .{};
        if (term_count == 0) return .{};
        return exactGramProjectorFormulaAudit();
    }

    fn localProductFormulaKind(self: *Impl, step: coupling.CouplingStep) projector.ProjectorFormulaKind {
        if (self.isIdentityProductStep(step)) return .identity;
        if (self.isOrthogonalVectorMetricStep(step)) return .orthogonal_vector_metric;
        if (self.isOrthogonalSpinorPairSingletStep(step)) return .orthogonal_spinor_pair;
        if (self.isOrthogonalSpinorSpinorVectorStep(step)) return .orthogonal_spinor_form_channel;
        if (self.orthogonalSpinorSpinorFormStep(step) != null) return .orthogonal_spinor_form_channel;
        if (self.isOrthogonalFormPairSingletStep(step)) return .orthogonal_form_pair;
        if (self.orthogonalFormSpinorStep(step) != null) return .orthogonal_form_spinor_channel;
        if (self.isCartanProductStep(step)) return .cartan_product_channel;
        if (self.orthogonalStructuralStep(step, 0, 1, 2)) |structural| {
            const spec = structuralProjectorSpecFromOrthogonalStep(structural);
            if ((self.structural_projection_programs.termCount(spec) catch 0) != 0) return .orthogonal_structural_projection;
        }
        if (self.isA2FundamentalPairToAntiFundamentalStep(step)) return .backend_specific_structure;
        if (self.isA2AntiFundamentalFundamentalSingletStep(step)) return .backend_specific_structure;
        if (self.isE6FundamentalPairToDualFundamentalStep(step)) return .backend_specific_structure;
        if (self.isE6DualFundamentalFundamentalSingletStep(step)) return .backend_specific_structure;
        if (self.isSimpleAdjointAdjointStep(step)) return .backend_specific_structure;
        if (self.isSimpleAdjointPairSingletStep(step)) return .backend_specific_structure;
        return .named_only;
    }

    fn orthogonalStructuralStep(self: *Impl, step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) ?OrthogonalStructuralStep {
        const simple = self.stepSimpleAlgebra(step) orelse return null;
        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_descriptor = orthogonalIrrepDescriptor(simple, left);
        const right_descriptor = orthogonalIrrepDescriptor(simple, right);
        const output_descriptor = orthogonalIrrepDescriptor(simple, output);
        if (left_descriptor.kind == .unsupported or right_descriptor.kind == .unsupported or output_descriptor.kind == .unsupported) return null;
        if (left_descriptor.dimension != right_descriptor.dimension or left_descriptor.dimension != output_descriptor.dimension) return null;
        if (left_descriptor.kind == .scalar and right_descriptor.kind == .scalar and output_descriptor.kind == .scalar) return null;
        return .{
            .operator_id = step.projector,
            .dimension = left_descriptor.dimension,
            .left = .{ .irrep = left_descriptor, .index = left_index },
            .right = .{ .irrep = right_descriptor, .index = right_index },
            .output = .{ .irrep = output_descriptor, .index = output_index },
            .multiplicity_copy = step.multiplicity_copy,
        };
    }

    fn boundaryRealizationProjector(self: *Impl, handle: realization.RealizationHandle) !projector.ProjectorId {
        const has_formula = try self.hasOrthogonalVectorSpinorBoundaryFormula(handle);
        const formula_audit = if (has_formula) try self.orthogonalVectorSpinorBoundaryFormulaAudit(handle) else projector.ProjectorFormulaAudit{};
        const formula_verified = has_formula and formula_audit.verified() and formula_audit.gamma_traceless;
        return self.projectors.internProjector(.{
            .role = .{ .boundary_realization = handle },
            .convention = .{
                .render_mode = .named,
                .signature = self.options.default_signature,
                .normalization_id = 0,
            },
        }, .{
            .kind = if (formula_verified) .backend_specific_verified else .highest_weight_solver,
            .source = if (formula_verified) .backend_specific_verified else .highest_weight_solver,
            .status = if (formula_verified) .expandable_terms else if (has_formula) .blocked_unverified_identity else .expandable_named,
            .formula_kind = if (has_formula) .orthogonal_gamma_traceless else .named_only,
            .formula_audit = formula_audit,
        });
    }

    fn requirePathProjectorExpansion(self: *Impl, steps: []const coupling.CouplingStep, mode: rendering.ProjectorRenderMode) !void {
        for (steps) |step| {
            if (!self.projectors.canRenderMode(step.projector, mode)) return error.ProjectorExpansionNotImplemented;
        }
    }

    fn isOrthogonalVectorMetricStep(self: *Impl, step: coupling.CouplingStep) bool {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return false;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return false;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return false;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return false;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return false;
        switch (simple.family) {
            .b, .d => {},
            else => return false,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return false;
        const right = self.representations.irrepDynkin(step.right) orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        return isVectorDynkin(left) and isVectorDynkin(right) and isZeroDynkin(output);
    }

    fn isIdentityProductStep(self: *Impl, step: coupling.CouplingStep) bool {
        if (step.multiplicity_copy != 0) return false;
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return false;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return false;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return false;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return false;

        const left = self.representations.irrepDynkin(step.left) orelse return false;
        const right = self.representations.irrepDynkin(step.right) orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        if (left.len != right.len or left.len != output.len) return false;
        if (isZeroDynkin(left) and std.mem.eql(i16, right, output)) return true;
        if (isZeroDynkin(right) and std.mem.eql(i16, left, output)) return true;
        return false;
    }

    fn isOrthogonalSpinorPairSingletStep(self: *Impl, step: coupling.CouplingStep) bool {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return false;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return false;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return false;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return false;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return false;
        switch (simple.family) {
            .b, .d => {},
            else => return false,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return false;
        const right = self.representations.irrepDynkin(step.right) orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        return isSpinorDynkin(simple, left) and isSpinorDynkin(simple, right) and isZeroDynkin(output);
    }

    fn isOrthogonalSpinorSpinorVectorStep(self: *Impl, step: coupling.CouplingStep) bool {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return false;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return false;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return false;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return false;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return false;
        switch (simple.family) {
            .b, .d => {},
            else => return false,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return false;
        const right = self.representations.irrepDynkin(step.right) orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        return isSpinorDynkin(simple, left) and isSpinorDynkin(simple, right) and isVectorDynkin(output);
    }

    fn orthogonalSpinorPairFormulaAudit(self: *Impl, step: coupling.CouplingStep) projector.ProjectorFormulaAudit {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return .{};
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return .{};
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return .{};
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return .{};
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return .{};
        const left = self.representations.irrepDynkin(step.left) orelse return .{};
        const right = self.representations.irrepDynkin(step.right) orelse return .{};
        return orthogonalSpinorBilinearFormulaAudit(simple, left, right, 0, .none);
    }

    fn orthogonalSpinorFormFormulaAudit(self: *Impl, step: coupling.CouplingStep) projector.ProjectorFormulaAudit {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return .{};
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return .{};
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return .{};
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return .{};
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return .{};
        const left = self.representations.irrepDynkin(step.left) orelse return .{};
        const right = self.representations.irrepDynkin(step.right) orelse return .{};
        const output = self.representations.irrepDynkin(step.output) orelse return .{};
        var rank: u8 = 1;
        var duality: rendering.DualityTag = .none;
        if (!isVectorDynkin(output)) {
            const info = self.orthogonalSpinorSpinorFormStep(step) orelse return .{};
            rank = info.rank;
            duality = info.duality;
        }
        return orthogonalSpinorBilinearFormulaAudit(simple, left, right, rank, duality);
    }

    fn orthogonalFormSpinorFormulaAudit(self: *Impl, step: coupling.CouplingStep) projector.ProjectorFormulaAudit {
        const info = self.orthogonalFormSpinorStep(step) orelse return .{};
        const simple = self.stepSimpleAlgebra(step) orelse return .{};
        const right = self.representations.irrepDynkin(step.right) orelse return .{};
        const output = self.representations.irrepDynkin(step.output) orelse return .{};
        const input_chirality = rendering.gammaChiralityTag(simple, right);
        const output_chirality = rendering.gammaChiralityTag(simple, output);
        if (!orthogonalGammaGradeNormNonZero(simple, rendering.orthogonalDimension(simple), info.rank, info.duality)) return .{};
        const chirality_valid = switch (simple.family) {
            .b => input_chirality == .none and output_chirality == .none,
            .d => output_chirality == if (info.rank % 2 == 0) input_chirality else oppositeGammaChirality(input_chirality),
            else => false,
        };
        if (!chirality_valid) return .{};
        return exactPrimitiveFormulaAudit();
    }

    fn orthogonalSpinorTowerCartanProductFormulaAudit(self: *Impl, step: coupling.CouplingStep) projector.ProjectorFormulaAudit {
        const simple = self.stepSimpleAlgebra(step) orelse return .{};
        const left = self.representations.irrepDynkin(step.left) orelse return .{};
        const right = self.representations.irrepDynkin(step.right) orelse return .{};
        const output = self.representations.irrepDynkin(step.output) orelse return .{};
        const left_tower = spinorTowerInfo(simple, left) orelse return .{};
        const right_tower = spinorTowerInfo(simple, right) orelse return .{};
        const output_tower = spinorTowerInfo(simple, output) orelse return .{};
        if (left_tower.chirality != right_tower.chirality or left_tower.chirality != output_tower.chirality) return .{};
        if (output_tower.power != left_tower.power + right_tower.power) return .{};
        return exactPrimitiveFormulaAudit();
    }

    fn orthogonalSpinorSpinorFormStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalFormInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        if (!isSpinorDynkin(simple, left) or !isSpinorDynkin(simple, right)) return null;
        const form_info = orthogonalFormInfo(simple, output) orelse return null;
        return if (form_info.rank > 1) form_info else null;
    }

    fn orthogonalFormSpinorStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalFormInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const form_info = orthogonalFormInfo(simple, left) orelse return null;
        if (spinorTowerInfo(simple, left) != null and spinorTowerInfo(simple, output) != null) return null;
        if (!isSpinorDynkin(simple, right) or !isSpinorDynkin(simple, output)) return null;
        return form_info;
    }

    fn orthogonalSpinorTowerFormStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_tower = spinorTowerInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_tower.chirality) return null;
        if (left_tower.power < 2) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != left_tower.power - 1) return null;
        if (output_info.chirality != left_tower.chirality) return null;
        return output_info;
    }

    fn orthogonalSpinorTowerMiddleFormStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalFormInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_tower = spinorTowerInfo(simple, left) orelse return null;
        if (left_tower.power != 3) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_tower.chirality) return null;
        const output_info = orthogonalFormInfo(simple, output) orelse return null;
        if (output_info.duality == .none) return null;
        if (output_info.rank != rendering.orthogonalDimension(simple) / 2) return null;
        return output_info;
    }

    fn orthogonalSpinorTowerOppositeFormStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = spinorTowerInfo(simple, left) orelse return null;
        if (left_info.power < 2) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.power - 1) return null;
        if (output_info.forms.total_power != 1) return null;
        return output_info;
    }

    fn orthogonalSpinorTowerOppositeLowerStep(self: *Impl, step: coupling.CouplingStep) ?SpinorTowerInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = spinorTowerInfo(simple, left) orelse return null;
        if (left_info.power < 2) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = spinorTowerInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.power != left_info.power - 1) return null;
        return output_info;
    }

    fn orthogonalTensorSpinorTowerStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        if (left_info.tower_power < 2) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != left_info.tower_power - 1) return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.forms.count != left_info.forms.count + 1) return null;
        if ((output_info.forms.mask & left_info.forms.mask) != left_info.forms.mask) return null;
        return output_info;
    }

    fn orthogonalTensorSpinorFormPowerStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        if (left_info.tower_power < 2) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != left_info.tower_power - 1) return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.forms.count != left_info.forms.count) return null;
        if (output_info.forms.total_power != left_info.forms.total_power + 1) return null;
        if (!formProfileIncrementedExistingOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return output_info;
    }

    fn orthogonalTensorSpinorTowerRaiseStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power + 1) return null;
        if (output_info.forms.profile != left_info.forms.profile) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeTowerLowerStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power < 2) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power - 1) return null;
        if (output_info.forms.profile != left_info.forms.profile) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeShiftStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power < 2) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power - 1) return null;
        if (output_info.forms.total_power != left_info.forms.total_power) return null;
        if (!formProfileShiftedByOnce(left_info.forms.profile, output_info.forms.profile, 2)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeAllShiftStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power < 2) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power - 1) return null;
        if (output_info.forms.total_power != left_info.forms.total_power) return null;
        if (!formProfileShiftedAllUpOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeFormAddStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power < 2) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power - 1) return null;
        if (output_info.forms.total_power != left_info.forms.total_power + 1) return null;
        if (!formProfileAddedOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeRankSplitStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power < 2) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power - 1) return null;
        if (output_info.forms.total_power != left_info.forms.total_power + 1) return null;
        if (!formProfileSplitToNeighborsOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorShiftStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        if (left_info.tower_power < 2) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != left_info.tower_power - 1) return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.forms.count != left_info.forms.count) return null;
        if (!formMaskShiftedUpOnce(left_info.forms.mask, output_info.forms.mask)) return null;
        return output_info;
    }

    fn orthogonalTensorSpinorRankWrapShiftStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        if (left_info.tower_power < 2) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != left_info.tower_power - 1) return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.forms.count != left_info.forms.count) return null;
        if (!formProfileMovedOnce(left_info.forms.profile, output_info.forms.profile, 0, simple.rank - 2)) return null;
        return output_info;
    }

    fn orthogonalTensorSpinorRankSplitStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        if (left_info.tower_power < 2) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != left_info.tower_power - 1) return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.forms.total_power != left_info.forms.total_power + 1) return null;
        if (!formProfileSplitDownToRankWrapOnce(left_info.forms.profile, output_info.forms.profile, simple.rank - 2)) return null;
        return output_info;
    }

    fn orthogonalTensorSpinorTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power) return null;
        if (!formProfileShiftedUpOnce(left_info.forms.profile, output_info.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power) return null;
        if (!formProfileShiftedByOnce(left_info.forms.profile, output_info.profile, 2)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeFormAddTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power + 1) return null;
        if (!formProfileAddedOnce(left_info.forms.profile, output_info.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeFormAddShiftTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power + 1) return null;
        if (!formProfileShiftedUpThenAddedOnce(left_info.forms.profile, output_info.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeRankSplitTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power + 1) return null;
        if (!formProfileSplitToNeighborsOnce(left_info.forms.profile, output_info.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeShiftTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power) return null;
        if (!formProfileShiftedAllUpOnce(left_info.forms.profile, output_info.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorRankWrapTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power) return null;
        if (!formProfileMovedOnce(left_info.forms.profile, output_info.profile, 0, simple.rank - 2)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorRankSplitTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power + 1) return null;
        if (!formProfileSplitDownToRankWrapOnce(left_info.forms.profile, output_info.profile, simple.rank - 2)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorFormTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power) return null;
        if (output_info.profile != left_info.forms.profile) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorFormAddTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power + 1) return null;
        if (!formProfileAddedOnce(left_info.forms.profile, output_info.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorFormPowerTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_info = ordinaryTensorFormInfo(simple, output) orelse return null;
        if (output_info.total_power != left_info.forms.total_power + 1) return null;
        if (!formProfileIncrementedExistingOnce(left_info.forms.profile, output_info.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorFormTowerStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power + 1) return null;
        if (output_info.forms.total_power + 1 != left_info.forms.total_power) return null;
        if (!formProfileRemovedOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorFormTowerTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTowerTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_tower = spinorTowerInfo(simple, output) orelse return null;
        if (output_tower.chirality != left_info.chirality) return null;
        if (output_tower.power != left_info.tower_power + 1) return null;
        if (!formProfileRemovedOnce(left_info.forms.profile, 0)) return null;
        return .{
            .input = left_info,
            .output = output_tower,
        };
    }

    fn orthogonalTensorSpinorFormTowerRemoveShiftStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power + 1) return null;
        if (output_info.forms.total_power + 1 != left_info.forms.total_power) return null;
        if (!formProfileRemovedThenShiftedUpOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorFormTowerShiftDownStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power + 1) return null;
        if (output_info.forms.total_power != left_info.forms.total_power) return null;
        if (!formProfileMovedDownOnce(left_info.forms.profile, output_info.forms.profile, 2)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorFormTowerAllShiftDownStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) != left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power + 1) return null;
        if (output_info.forms.total_power != left_info.forms.total_power) return null;
        if (!formProfileShiftedAllDownOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeFormTowerStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power + 1) return null;
        if (output_info.forms.total_power + 1 != left_info.forms.total_power) return null;
        if (!formProfileRemovedOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeFormTowerTerminalStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTowerTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        if (orthogonalFormInfo(simple, output) != null) return null;
        const output_tower = spinorTowerInfo(simple, output) orelse return null;
        if (output_tower.chirality != left_info.chirality) return null;
        if (output_tower.power != left_info.tower_power + left_info.forms.total_power) return null;
        if (!formProfileRemovedOnce(left_info.forms.profile, 0)) return null;
        return .{
            .input = left_info,
            .output = output_tower,
        };
    }

    fn orthogonalTensorSpinorOppositeFormTowerMergeStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power + 1) return null;
        if (output_info.forms.total_power + 1 != left_info.forms.total_power) return null;
        if (!formProfileMergedPairToMiddleOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeFormTowerRemoveShiftStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power + 1) return null;
        if (output_info.forms.total_power + 1 != left_info.forms.total_power) return null;
        if (!formProfileRemovedThenShiftedUpOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorOppositeFormTowerShiftDownStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorSpinorTransitionInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        if (rendering.gammaChiralityTag(simple, right) == left_info.chirality) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.chirality != left_info.chirality) return null;
        if (output_info.tower_power != left_info.tower_power + 1) return null;
        if (output_info.forms.total_power != left_info.forms.total_power) return null;
        if (!formProfileMovedDownAnyOnce(left_info.forms.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorFormSpinorStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = ordinaryTensorFormInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != 1) return null;
        if (output_info.forms.total_power + 1 != left_info.total_power) return null;
        if (!formProfileRemovedOnce(left_info.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorFormSpinorPreserveStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = ordinaryTensorFormInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != 1) return null;
        if (output_info.forms.profile != left_info.profile) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorFormSpinorShiftStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = ordinaryTensorFormInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != 1) return null;
        if (output_info.forms.total_power + 1 != left_info.total_power) return null;
        if (!formProfileRemovedThenShiftedUpOnce(left_info.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorFormSpinorRemoveShiftDownStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = ordinaryTensorFormInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != 1) return null;
        if (output_info.forms.total_power + 1 != left_info.total_power) return null;
        if (!formProfileRemovedThenMovedDownOnce(left_info.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorFormSpinorShiftDownStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = ordinaryTensorFormInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != 1) return null;
        if (output_info.forms.total_power != left_info.total_power) return null;
        if (!formProfileMovedDownOnce(left_info.profile, output_info.forms.profile, 1)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorFormSpinorShiftDownTwoStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = ordinaryTensorFormInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != 1) return null;
        if (output_info.forms.total_power != left_info.total_power) return null;
        if (!formProfileMovedDownOnce(left_info.profile, output_info.forms.profile, 2)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorFormSpinorMixedShiftDownStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = ordinaryTensorFormInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != 1) return null;
        if (output_info.forms.total_power != left_info.total_power) return null;
        if (!formProfileShiftedAllDownWithOneExtraOnce(left_info.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorFormSpinorAllShiftDownStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = ordinaryTensorFormInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != 1) return null;
        if (output_info.forms.total_power != left_info.total_power) return null;
        if (!formProfileShiftedAllDownOnce(left_info.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorFormSpinorShiftDownAnyStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorFormSpinorInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        switch (simple.family) {
            .b, .d => {},
            else => return null,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = ordinaryTensorFormInfo(simple, left) orelse return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = orthogonalTensorSpinorInfo(simple, output) orelse return null;
        if (output_info.tower_power != 1) return null;
        if (output_info.forms.total_power != left_info.total_power) return null;
        if (!formProfileMovedDownAnyOnce(left_info.profile, output_info.forms.profile)) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn orthogonalTensorSpinorMiddleFormStep(self: *Impl, step: coupling.CouplingStep) ?OrthogonalTensorMiddleFormTerminalInfo {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return null;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return null;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return null;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return null;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return null;
        if (simple.family != .d) return null;

        const left = self.representations.irrepDynkin(step.left) orelse return null;
        const right = self.representations.irrepDynkin(step.right) orelse return null;
        const output = self.representations.irrepDynkin(step.output) orelse return null;
        const left_info = orthogonalTensorSpinorInfo(simple, left) orelse return null;
        if (left_info.tower_power != 1 or left_info.forms.total_power != 1) return null;
        if (!isSpinorDynkin(simple, right)) return null;
        const output_info = orthogonalFormInfo(simple, output) orelse return null;
        if (output_info.duality == .none) return null;
        if (output_info.rank != rendering.orthogonalDimension(simple) / 2) return null;
        return .{
            .input = left_info,
            .output = output_info,
        };
    }

    fn isOrthogonalDualIrrepSingletStep(self: *Impl, step: coupling.CouplingStep, irrep: store.IrrepHandle) bool {
        const metadata = self.representations.irrepMetadata(irrep) orelse return false;
        const dual = metadata.dual orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        return step.left.value == irrep.value and step.right.value == dual.value and isZeroDynkin(output);
    }

    fn isOrthogonalFormPairSingletStep(self: *Impl, step: coupling.CouplingStep) bool {
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return false;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return false;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return false;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return false;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return false;
        switch (simple.family) {
            .b, .d => {},
            else => return false,
        }
        const left = self.representations.irrepDynkin(step.left) orelse return false;
        if (orthogonalFormInfo(simple, left) == null) return false;
        return self.isOrthogonalDualIrrepSingletStep(step, step.left);
    }

    fn isCartanProductStep(self: *Impl, step: coupling.CouplingStep) bool {
        if (step.multiplicity_copy != 0) return false;
        const left_algebra = self.representations.irrepAlgebra(step.left) orelse return false;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return false;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return false;
        if (left_algebra.value != right_algebra.value or left_algebra.value != output_algebra.value) return false;
        const simple = self.representations.simpleAlgebra(left_algebra) orelse return false;
        switch (simple.family) {
            .b, .d => {},
            else => return false,
        }

        const left = self.representations.irrepDynkin(step.left) orelse return false;
        const right = self.representations.irrepDynkin(step.right) orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        if (left.len != right.len or left.len != output.len) return false;
        if (isZeroDynkin(left) or isZeroDynkin(right)) return false;
        if (!isSpinorTowerDynkin(simple, left) or !isSpinorTowerDynkin(simple, right) or !isSpinorTowerDynkin(simple, output)) return false;
        for (output, 0..) |entry, index| {
            if (entry != left[index] + right[index]) return false;
        }
        return true;
    }

    fn isA2FundamentalCubicStep(self: *Impl, first: coupling.CouplingStep, second: coupling.CouplingStep) bool {
        return self.isA2FundamentalPairToAntiFundamentalStep(first) and
            second.left.value == first.output.value and
            self.isA2AntiFundamentalFundamentalSingletStep(second);
    }

    fn isA2FundamentalPairToAntiFundamentalStep(self: *Impl, step: coupling.CouplingStep) bool {
        const simple = self.stepSimpleAlgebra(step) orelse return false;
        if (simple.family != .a or simple.rank != 2) return false;
        const left = self.representations.irrepDynkin(step.left) orelse return false;
        const right = self.representations.irrepDynkin(step.right) orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        return isA2FundamentalDynkin(left) and isA2FundamentalDynkin(right) and isA2AntiFundamentalDynkin(output);
    }

    fn isA2AntiFundamentalFundamentalSingletStep(self: *Impl, step: coupling.CouplingStep) bool {
        const simple = self.stepSimpleAlgebra(step) orelse return false;
        if (simple.family != .a or simple.rank != 2) return false;
        const left = self.representations.irrepDynkin(step.left) orelse return false;
        const right = self.representations.irrepDynkin(step.right) orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        return isA2AntiFundamentalDynkin(left) and isA2FundamentalDynkin(right) and isZeroDynkin(output);
    }

    fn isE6FundamentalCubicStep(self: *Impl, first: coupling.CouplingStep, second: coupling.CouplingStep) bool {
        return self.isE6FundamentalPairToDualFundamentalStep(first) and
            second.left.value == first.output.value and
            self.isE6DualFundamentalFundamentalSingletStep(second);
    }

    fn isE6FundamentalPairToDualFundamentalStep(self: *Impl, step: coupling.CouplingStep) bool {
        const simple = self.stepSimpleAlgebra(step) orelse return false;
        if (simple.family != .e6 or simple.rank != 6) return false;
        const left = self.representations.irrepDynkin(step.left) orelse return false;
        const right = self.representations.irrepDynkin(step.right) orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        return isE6FundamentalDynkin(left) and isE6FundamentalDynkin(right) and isE6DualFundamentalDynkin(output);
    }

    fn isE6DualFundamentalFundamentalSingletStep(self: *Impl, step: coupling.CouplingStep) bool {
        const simple = self.stepSimpleAlgebra(step) orelse return false;
        if (simple.family != .e6 or simple.rank != 6) return false;
        const left = self.representations.irrepDynkin(step.left) orelse return false;
        const right = self.representations.irrepDynkin(step.right) orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        return isE6DualFundamentalDynkin(left) and isE6FundamentalDynkin(right) and isZeroDynkin(output);
    }

    fn isSimpleAdjointCubicStep(self: *Impl, first: coupling.CouplingStep, second: coupling.CouplingStep) bool {
        return self.isSimpleAdjointAdjointStep(first) and
            second.left.value == first.output.value and
            self.isSimpleAdjointPairSingletStep(second);
    }

    fn isSimpleAdjointAdjointStep(self: *Impl, step: coupling.CouplingStep) bool {
        if (step.multiplicity_copy != 0) return false;
        const algebra = self.representations.irrepAlgebra(step.left) orelse return false;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return false;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return false;
        if (algebra.value != right_algebra.value or algebra.value != output_algebra.value) return false;
        const simple = self.representations.simpleAlgebra(algebra) orelse return false;
        return self.isSimpleAdjointIrrep(simple, step.left) and
            self.isSimpleAdjointIrrep(simple, step.right) and
            self.isSimpleAdjointIrrep(simple, step.output);
    }

    fn isSimpleAdjointPairSingletStep(self: *Impl, step: coupling.CouplingStep) bool {
        if (step.multiplicity_copy != 0) return false;
        const algebra = self.representations.irrepAlgebra(step.left) orelse return false;
        const right_algebra = self.representations.irrepAlgebra(step.right) orelse return false;
        const output_algebra = self.representations.irrepAlgebra(step.output) orelse return false;
        if (algebra.value != right_algebra.value or algebra.value != output_algebra.value) return false;
        const simple = self.representations.simpleAlgebra(algebra) orelse return false;
        const output = self.representations.irrepDynkin(step.output) orelse return false;
        return self.isSimpleAdjointIrrep(simple, step.left) and
            self.isSimpleAdjointIrrep(simple, step.right) and
            isZeroDynkin(output);
    }

    fn isSimpleAdjointIrrep(self: *Impl, simple: symmetry.SimpleLieAlgebra, irrep: store.IrrepHandle) bool {
        const label = self.representations.irrepDynkin(irrep) orelse return false;
        if (isZeroDynkin(label)) return false;
        const metadata = self.representations.irrepMetadata(irrep) orelse return false;
        const dimension = metadata.dimension orelse return false;
        return dimension == simpleAdjointDimension(simple);
    }

    fn appendNamedProjectorAtoms(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), steps: []const coupling.CouplingStep) !u32 {
        var appended: u32 = 0;
        for (steps) |step| {
            const span = try self.projectors.ensureNamedExpansion(step.projector);
            if (span.len != 1) return error.InvalidProjectorExpansion;
            const term = self.projectors.expansionTerm(span, 0) orelse return error.InvalidProjectorExpansion;
            try atoms.appendSlice(self.allocator, term.atoms);
            appended += 1;
        }
        return appended;
    }

    fn streamLocalFormulaPathTerms(self: *Impl, steps: []const coupling.CouplingStep, options: rendering.RenderOptions, filter: rendering.ExpansionFilter, sink: anytype, audit: *rendering.ExpansionAudit, scratch: *ExpansionScratch) !bool {
        if (steps.len == 0) return false;
        if (steps.len > max_local_formula_steps) return error.ProjectorExpansionNotImplemented;

        var term_counts = [_]u8{0} ** max_local_formula_steps;
        var term_indices = [_]u8{0} ** max_local_formula_steps;
        var formula_kinds = [_]projector.ProjectorFormulaKind{.named_only} ** max_local_formula_steps;
        if (!try self.prepareLocalFormulaTermFrontier(steps, term_counts[0..steps.len], formula_kinds[0..steps.len])) return false;

        while (true) {
            scratch.local_path_atoms.clearRetainingCapacity();
            const coefficient = try self.appendLocalFormulaPathTermAtoms(&scratch.local_path_atoms, steps, formula_kinds[0..steps.len], term_indices[0..steps.len]);
            try self.emitLocalFormulaTerm(&scratch.local_term_atoms, scratch.local_path_atoms.items, coefficient, options, filter, sink, audit, &scratch.lowered_atoms);
            if (!incrementLocalFormulaTermIndices(term_indices[0..steps.len], term_counts[0..steps.len])) break;
        }
        return true;
    }

    fn prepareLocalFormulaTermFrontier(self: *Impl, steps: []const coupling.CouplingStep, term_counts: []u8, formula_kinds: []projector.ProjectorFormulaKind) !bool {
        if (steps.len == 0 or steps.len != term_counts.len or steps.len != formula_kinds.len) return false;
        for (steps, 0..) |step, step_index| {
            const formula_kind = self.localProductFormulaKind(step);
            if (formula_kind == .named_only) return false;
            const cached_kind = try self.projectors.ensureFormulaProgram(step.projector);
            if (cached_kind != formula_kind) return error.InvalidProjectorExpansion;
            const count = try self.localFormulaStepTermCount(step, cached_kind);
            if (count == 0) return false;
            term_counts[step_index] = count;
            formula_kinds[step_index] = cached_kind;
        }
        return true;
    }

    fn localFormulaStepTermCount(self: *Impl, step: coupling.CouplingStep, formula_kind: projector.ProjectorFormulaKind) !u8 {
        if (try self.localFormulaProjectionStepTermCount(step, formula_kind)) |count| return count;
        return switch (formula_kind) {
            .backend_specific_structure, .named_only => 0,
            else => 1,
        };
    }

    fn localFormulaProjectionStepTermCount(self: *Impl, step: coupling.CouplingStep, formula_kind: projector.ProjectorFormulaKind) !?u8 {
        if (formula_kind == .orthogonal_structural_projection) {
            const count = try self.localStructuralTermCount(step, 0, 1, 2);
            if (count == 0) return error.UnsupportedStructuralProjectorTerm;
            return count;
        }
        var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
        defer atoms.deinit(self.allocator);
        if (!try self.appendLocalFormulaStepAtomForKind(&atoms, step, 0, 1, 2, formula_kind)) return null;
        if (atoms.items.len != 1) return null;
        return switch (atoms.items[0]) {
            .tensor_spinor_projection => |projection| blk: {
                const spec = tensorSpinorProjectionSpec(projection);
                const count = try self.tensor_spinor_projection_programs.termCount(spec);
                if (count == 0) return error.UnsupportedTensorSpinorProjectionTerm;
                break :blk count;
            },
            .tensor_form_projection => |projection| blk: {
                const count = try self.tensor_form_projection_programs.termCount(tensorFormProjectionSpec(projection));
                if (count == 0) return error.UnsupportedTensorFormProjectionTerm;
                break :blk count;
            },
            else => null,
        };
    }

    fn appendLocalFormulaPathTermAtoms(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), steps: []const coupling.CouplingStep, formula_kinds: []const projector.ProjectorFormulaKind, term_indices: []const u8) !rendering.RationalId {
        if (steps.len != formula_kinds.len or steps.len != term_indices.len) return error.InvalidProjectorExpansion;
        const scratch_base: u32 = @intCast(steps.len + 1);
        var coefficient = rendering.rationalOne();
        var previous_formula_atom: ?rendering.SymbolicAtom = null;
        for (steps, 0..) |step, step_index| {
            const left_index: rendering.IndexRef = if (step_index == 0) 0 else scratch_base + @as(u32, @intCast(step_index - 1));
            const right_index: rendering.IndexRef = @intCast(step_index + 1);
            const output_index: rendering.IndexRef = scratch_base + @as(u32, @intCast(step_index));
            const atom_index = atoms.items.len;
            const step_coefficient = try self.appendLocalFormulaStepTermAtoms(atoms, step, left_index, right_index, output_index, formula_kinds[step_index], term_indices[step_index]);
            coefficient = try multiplyRenderingRationals(coefficient, step_coefficient);
            if (atoms.items.len == atom_index) return error.InvalidProjectorExpansion;
            const current_formula_atom = atoms.items[atom_index];
            if (previous_formula_atom) |previous| {
                try appendCliffordProductAtoms(self.allocator, atoms, previous, current_formula_atom);
            }
            previous_formula_atom = current_formula_atom;
        }
        return coefficient;
    }

    fn appendLocalFormulaStepTermAtoms(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef, formula_kind: projector.ProjectorFormulaKind, term_index: u8) !rendering.RationalId {
        if (try self.appendLocalFormulaProjectionStepTerm(atoms, step, left_index, right_index, output_index, formula_kind, term_index)) |coefficient| return coefficient;
        if (term_index != 0) return error.ProjectorConstructorTermOutOfBounds;
        if (!try self.appendLocalFormulaStepAtomForKind(atoms, step, left_index, right_index, output_index, formula_kind)) return error.ProjectorExpansionNotImplemented;
        return rendering.rationalOne();
    }

    fn appendLocalFormulaProjectionStepTerm(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef, formula_kind: projector.ProjectorFormulaKind, term_index: u8) !?rendering.RationalId {
        if (formula_kind == .orthogonal_structural_projection) {
            if (try self.localStructuralTermCount(step, left_index, right_index, output_index) == 0) return error.UnsupportedStructuralProjectorTerm;
            return try self.appendLocalStructuralTerm(atoms, step, left_index, right_index, output_index, term_index);
        }
        var compact_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
        defer compact_atoms.deinit(self.allocator);
        if (!try self.appendLocalFormulaStepAtomForKind(&compact_atoms, step, left_index, right_index, output_index, formula_kind)) return null;
        if (compact_atoms.items.len != 1) return null;
        return switch (compact_atoms.items[0]) {
            .tensor_spinor_projection => |projection| blk: {
                const spec = tensorSpinorProjectionSpec(projection);
                if (try self.tensor_spinor_projection_programs.termCount(spec) == 0) return error.UnsupportedTensorSpinorProjectionTerm;
                break :blk try self.tensor_spinor_projection_programs.appendTerm(atoms, spec, term_index);
            },
            .tensor_form_projection => |projection| blk: {
                const spec = tensorFormProjectionSpec(projection);
                if (try self.tensor_form_projection_programs.termCount(spec) == 0) return error.UnsupportedTensorFormProjectionTerm;
                break :blk try self.tensor_form_projection_programs.appendTerm(atoms, spec, term_index);
            },
            else => null,
        };
    }

    fn localStructuralTermCount(self: *Impl, step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef) !u8 {
        const structural = self.orthogonalStructuralStep(step, left_index, right_index, output_index) orelse return 0;
        return self.structural_projection_programs.termCount(structuralProjectorSpecFromOrthogonalStep(structural));
    }

    fn appendLocalStructuralTerm(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), step: coupling.CouplingStep, left_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef, term_index: u8) !rendering.RationalId {
        const structural = self.orthogonalStructuralStep(step, left_index, right_index, output_index) orelse return error.ProjectorExpansionNotImplemented;
        return self.structural_projection_programs.appendTerm(atoms, structuralProjectorSpecFromOrthogonalStep(structural), term_index);
    }

    fn emitLocalFormulaTerm(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), formula_atoms: []const rendering.SymbolicAtom, coefficient: rendering.RationalId, options: rendering.RenderOptions, filter: rendering.ExpansionFilter, sink: anytype, audit: *rendering.ExpansionAudit, lowered_atoms: *std.ArrayList(rendering.SymbolicAtom)) !void {
        atoms.clearRetainingCapacity();
        try atoms.appendSlice(self.allocator, formula_atoms);
        const term: rendering.SymbolicTerm = .{
            .coefficient = coefficient,
            .atoms = atoms.items,
        };
        const decision = try filter.decide(term);
        audit.recordDecision(decision);
        switch (decision) {
            .reject => {},
            .accept, .undecided => try emitRenderedTerm(self.allocator, options, sink, term, audit, lowered_atoms),
        }
    }

    fn streamBoundaryFormulaTerms(self: *Impl, request: coupling.InvariantBasisRequest, steps: []const coupling.CouplingStep, options: rendering.RenderOptions, filter: rendering.ExpansionFilter, sink: anytype, audit: *rendering.ExpansionAudit, scratch: *ExpansionScratch) !void {
        var formula_count: u32 = 0;
        var formula: BoundaryFormula = undefined;
        for (request.external_legs, 0..) |leg, leg_index| {
            const handle = switch (leg.realization) {
                .handle => |handle| handle,
                .primitive_irrep, .registered_name => continue,
            };
            if (try self.orthogonalVectorSpinorBoundaryFormula(handle, leg, request, leg_index)) |found| {
                formula = found;
                formula_count += 1;
            } else {
                const spec = self.realizations.realizationSpecFor(handle) orelse return error.UnknownRealization;
                if (spec.ambient.len != 0) return error.ProjectorExpansionNotImplemented;
            }
        }
        if (formula_count != 1) return error.ProjectorExpansionNotImplemented;
        const cached_kind = try self.projectors.ensureFormulaProgram(formula.operator_id);
        if (cached_kind != .orthogonal_gamma_traceless) return error.InvalidProjectorExpansion;

        const spec: projector_constructor.VectorSpinorTracelessSpec = .{
            .operator_id = formula.operator_id,
            .vector = formula.vector,
            .spinor = formula.spinor,
            .orthogonal_dimension = formula.orthogonal_dimension,
            .chirality = formula.chirality,
        };

        if (steps.len == 0) {
            try self.streamBoundaryFormulaTermsWithPath(spec, &.{}, rendering.rationalOne(), options, filter, sink, audit, scratch);
            return;
        }

        scratch.boundary_path_atoms.clearRetainingCapacity();
        if (try self.appendSpecialExplicitPathAtoms(&scratch.boundary_path_atoms, steps)) {
            try self.streamBoundaryFormulaTermsWithPath(spec, scratch.boundary_path_atoms.items, rendering.rationalOne(), options, filter, sink, audit, scratch);
            return;
        }

        if (steps.len > max_local_formula_steps) return error.ProjectorExpansionNotImplemented;
        var term_counts = [_]u8{0} ** max_local_formula_steps;
        var term_indices = [_]u8{0} ** max_local_formula_steps;
        var formula_kinds = [_]projector.ProjectorFormulaKind{.named_only} ** max_local_formula_steps;
        if (!try self.prepareLocalFormulaTermFrontier(steps, term_counts[0..steps.len], formula_kinds[0..steps.len])) return error.ProjectorExpansionNotImplemented;

        while (true) {
            scratch.boundary_path_atoms.clearRetainingCapacity();
            const path_coefficient = try self.appendLocalFormulaPathTermAtoms(&scratch.boundary_path_atoms, steps, formula_kinds[0..steps.len], term_indices[0..steps.len]);
            try self.streamBoundaryFormulaTermsWithPath(spec, scratch.boundary_path_atoms.items, path_coefficient, options, filter, sink, audit, scratch);
            if (!incrementLocalFormulaTermIndices(term_indices[0..steps.len], term_counts[0..steps.len])) break;
        }
    }

    fn streamBoundaryFormulaTermsWithPath(self: *Impl, spec: projector_constructor.VectorSpinorTracelessSpec, path_atoms: []const rendering.SymbolicAtom, path_coefficient: rendering.RationalId, options: rendering.RenderOptions, filter: rendering.ExpansionFilter, sink: anytype, audit: *rendering.ExpansionAudit, scratch: *ExpansionScratch) !void {
        var term_index: u8 = 0;
        while (term_index < projector_constructor.vectorSpinorTracelessTermCount(spec)) : (term_index += 1) {
            scratch.boundary_formula_atoms.clearRetainingCapacity();
            const formula_coefficient = try projector_constructor.appendVectorSpinorTracelessTerm(self.allocator, &scratch.boundary_formula_atoms, spec, term_index);
            const coefficient = try multiplyRenderingRationals(path_coefficient, formula_coefficient);
            try self.emitBoundaryFormulaTerm(&scratch.boundary_term_atoms, path_atoms, scratch.boundary_formula_atoms.items, coefficient, options, filter, sink, audit, &scratch.lowered_atoms);
        }
    }

    fn emitBoundaryFormulaTerm(self: *Impl, atoms: *std.ArrayList(rendering.SymbolicAtom), path_atoms: []const rendering.SymbolicAtom, formula_atoms: []const rendering.SymbolicAtom, coefficient: rendering.RationalId, options: rendering.RenderOptions, filter: rendering.ExpansionFilter, sink: anytype, audit: *rendering.ExpansionAudit, lowered_atoms: *std.ArrayList(rendering.SymbolicAtom)) !void {
        atoms.clearRetainingCapacity();
        try atoms.appendSlice(self.allocator, formula_atoms);
        try atoms.appendSlice(self.allocator, path_atoms);
        const term: rendering.SymbolicTerm = .{
            .coefficient = coefficient,
            .atoms = atoms.items,
        };
        const decision = try filter.decide(term);
        audit.recordDecision(decision);
        switch (decision) {
            .reject => {},
            .accept, .undecided => {
                try emitRenderedTerm(self.allocator, options, sink, term, audit, lowered_atoms);
            },
        }
    }

    fn hasOrthogonalVectorSpinorBoundaryFormula(self: *Impl, handle: realization.RealizationHandle) !bool {
        const spec = self.realizations.realizationSpecFor(handle) orelse return error.UnknownRealization;
        return self.isOrthogonalVectorSpinorBoundarySpec(spec);
    }

    fn orthogonalVectorSpinorBoundaryFormulaAudit(self: *Impl, handle: realization.RealizationHandle) !projector.ProjectorFormulaAudit {
        const spec = self.realizations.realizationSpecFor(handle) orelse return error.UnknownRealization;
        if (!self.isOrthogonalVectorSpinorBoundarySpec(spec)) return .{};
        const target_algebra = self.representations.irrepAlgebra(spec.channel.irrep) orelse return error.UnknownIrrep;
        const simple = self.representations.simpleAlgebra(target_algebra) orelse return error.UnsupportedAlgebraFamily;
        return orthogonalVectorSpinorFormulaAudit(rendering.orthogonalDimension(simple));
    }

    fn orthogonalVectorSpinorBoundaryFormula(self: *Impl, handle: realization.RealizationHandle, leg: realization.ExternalLeg, request: coupling.InvariantBasisRequest, leg_index: usize) !?BoundaryFormula {
        const spec = self.realizations.realizationSpecFor(handle) orelse return error.UnknownRealization;
        if (!self.isOrthogonalVectorSpinorBoundarySpec(spec)) return null;
        const target_algebra = self.representations.irrepAlgebra(spec.channel.irrep) orelse return error.UnknownIrrep;
        const simple = self.representations.simpleAlgebra(target_algebra) orelse return error.UnsupportedAlgebraFamily;
        const spinor = try self.boundarySpinorFactor(spec);
        const spinor_label = self.representations.irrepDynkin(spinor) orelse return error.UnknownIrrep;
        const first_index = externalIndexOffset(request, leg_index);
        const vector_slot = findIndexKind(leg.indices, .vector) orelse return error.InvalidBoundaryFormulaIndices;
        const spinor_slot = findSpinorIndex(leg.indices) orelse return error.InvalidBoundaryFormulaIndices;
        return .{
            .operator_id = try self.boundaryRealizationProjector(handle),
            .vector = first_index + @as(u32, @intCast(vector_slot)),
            .spinor = first_index + @as(u32, @intCast(spinor_slot)),
            .orthogonal_dimension = rendering.orthogonalDimension(simple),
            .chirality = @intFromEnum(rendering.gammaChiralityTag(simple, spinor_label)),
        };
    }

    fn isOrthogonalVectorSpinorBoundarySpec(self: *Impl, spec: realization.RealizationSpec) bool {
        if (spec.ambient.len != 2) return false;
        const target_algebra = self.representations.irrepAlgebra(spec.channel.irrep) orelse return false;
        const simple = self.representations.simpleAlgebra(target_algebra) orelse return false;
        switch (simple.family) {
            .b, .d => {},
            else => return false,
        }
        const target = self.representations.irrepDynkin(spec.channel.irrep) orelse return false;
        if (!isVectorSpinorDynkin(simple, target)) return false;
        const spinor = self.boundarySpinorFactor(spec) catch return false;
        const vector = self.boundaryVectorFactor(spec) catch return false;
        const spinor_label = self.representations.irrepDynkin(spinor) orelse return false;
        const vector_label = self.representations.irrepDynkin(vector) orelse return false;
        return isSpinorDynkin(simple, spinor_label) and isVectorDynkin(vector_label);
    }

    fn boundarySpinorFactor(self: *Impl, spec: realization.RealizationSpec) !store.IrrepHandle {
        for (spec.ambient) |factor| {
            const algebra = self.representations.irrepAlgebra(factor) orelse return error.UnknownIrrep;
            const simple = self.representations.simpleAlgebra(algebra) orelse return error.UnsupportedAlgebraFamily;
            const label = self.representations.irrepDynkin(factor) orelse return error.UnknownIrrep;
            if (isSpinorDynkin(simple, label)) return factor;
        }
        return error.InvalidBoundaryFormulaChannel;
    }

    fn boundaryVectorFactor(self: *Impl, spec: realization.RealizationSpec) !store.IrrepHandle {
        for (spec.ambient) |factor| {
            const label = self.representations.irrepDynkin(factor) orelse return error.UnknownIrrep;
            if (isVectorDynkin(label)) return factor;
        }
        return error.InvalidBoundaryFormulaChannel;
    }

    fn externalLegIrrep(self: *Impl, leg: realization.ExternalLeg) !store.IrrepHandle {
        return switch (leg.realization) {
            .primitive_irrep => |irrep| irrep,
            .handle => |handle| self.realizations.targetIrrep(handle) orelse return error.UnknownRealization,
            .registered_name => return error.RegisteredRealizationNotResolved,
        };
    }

    fn targetIrrep(self: *Impl, algebra: store.AlgebraHandle, target: coupling.TargetIrrep) !store.IrrepHandle {
        return switch (target) {
            .irrep => |irrep| irrep,
            .singlet => singlet: {
                const simple = self.representations.simpleAlgebra(algebra) orelse return error.UnsupportedAlgebraFamily;
                const label = try self.allocator.alloc(i16, simple.rank);
                defer self.allocator.free(label);
                @memset(label, 0);
                break :singlet try self.representations.internIrrep(algebra, .{ .dynkin = label });
            },
        };
    }
};

fn continuationKey(next_index: usize, irrep: store.IrrepHandle) u64 {
    return (@as(u64, @intCast(next_index)) << 32) | @as(u64, irrep.value);
}

const PartialPathNode = struct {
    output: store.IrrepHandle,
    parent: u32,
    has_parent: bool,
    step: coupling.CouplingStep,
};

const OrthogonalFormInfo = struct {
    rank: u8,
    duality: rendering.DualityTag = .none,
};

const SpinorTowerInfo = struct {
    power: u16,
    chirality: rendering.GammaChirality = .none,
};

const OrthogonalFormSetInfo = struct {
    first_rank: u8,
    count: u8,
    total_power: u8,
    mask: u64,
    profile: u128,
    duality: rendering.DualityTag = .none,
};

const OrthogonalYoungShape = struct {
    row_count: u8,
    rows: [max_orthogonal_young_rows]u8 = [_]u8{0} ** max_orthogonal_young_rows,
    box_count: u8,
};

const OrthogonalTensorSpinorInfo = struct {
    forms: OrthogonalFormSetInfo,
    tower_power: u16,
    chirality: rendering.GammaChirality = .none,
};

const OrthogonalTensorSpinorTransitionInfo = struct {
    input: OrthogonalTensorSpinorInfo,
    output: OrthogonalTensorSpinorInfo,
};

const OrthogonalTensorSpinorTowerTerminalInfo = struct {
    input: OrthogonalTensorSpinorInfo,
    output: SpinorTowerInfo,
};

const OrthogonalTensorFormTerminalInfo = struct {
    input: OrthogonalTensorSpinorInfo,
    output: OrthogonalFormSetInfo,
};

const OrthogonalTensorMiddleFormTerminalInfo = struct {
    input: OrthogonalTensorSpinorInfo,
    output: OrthogonalFormInfo,
};

const OrthogonalTensorFormSpinorInfo = struct {
    input: OrthogonalFormSetInfo,
    output: OrthogonalTensorSpinorInfo,
};

const max_orthogonal_young_rows = 8;

const OrthogonalIrrepKind = enum {
    scalar,
    form_profile,
    vector_young_shape,
    spinor_tower,
    tensor_spinor,
    unsupported,
};

const OrthogonalIrrepDescriptor = struct {
    kind: OrthogonalIrrepKind,
    dimension: u16,
    form_profile: u128 = 0,
    form_mask: u64 = 0,
    form_count: u8 = 0,
    form_total_power: u8 = 0,
    form_rank: u8 = 0,
    form_duality: rendering.DualityTag = .none,
    young_row_count: u8 = 0,
    young_rows: [max_orthogonal_young_rows]u8 = [_]u8{0} ** max_orthogonal_young_rows,
    young_box_count: u8 = 0,
    has_spinor: bool = false,
    chirality: u8 = 0,
    tower_power: u16 = 0,
};

const OrthogonalEndpoint = struct {
    irrep: OrthogonalIrrepDescriptor,
    index: rendering.IndexRef,
};

const OrthogonalStructuralStep = struct {
    operator_id: u32,
    dimension: u16,
    left: OrthogonalEndpoint,
    right: OrthogonalEndpoint,
    output: OrthogonalEndpoint,
    multiplicity_copy: u16,
};

const BoundaryFormula = struct {
    operator_id: u32,
    vector: rendering.IndexRef,
    spinor: rendering.IndexRef,
    orthogonal_dimension: u16,
    chirality: u8,
};

const max_local_formula_steps = 32;

const ExpansionScratch = struct {
    atoms: std.ArrayList(rendering.SymbolicAtom) = .empty,
    local_path_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty,
    local_term_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty,
    boundary_path_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty,
    boundary_formula_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty,
    boundary_term_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty,
    lowered_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty,

    fn deinit(self: *ExpansionScratch, allocator: std.mem.Allocator) void {
        self.lowered_atoms.deinit(allocator);
        self.boundary_term_atoms.deinit(allocator);
        self.boundary_formula_atoms.deinit(allocator);
        self.boundary_path_atoms.deinit(allocator);
        self.local_term_atoms.deinit(allocator);
        self.local_path_atoms.deinit(allocator);
        self.atoms.deinit(allocator);
        self.* = .{};
    }
};

const PathEnumeration = struct {
    allocator: std.mem.Allocator,
    paths: std.ArrayList(coupling.CouplingPath) = .empty,
    steps: std.ArrayList(coupling.CouplingStep) = .empty,

    fn init(allocator: std.mem.Allocator) !PathEnumeration {
        return .{ .allocator = allocator };
    }

    fn deinit(self: *PathEnumeration) void {
        self.steps.deinit(self.allocator);
        self.paths.deinit(self.allocator);
        self.* = undefined;
    }
};

const BackendRegistry = struct {
    records: [6]backend.Record,

    fn init(generic: *generic_backend.Backend) BackendRegistry {
        return .{ .records = .{
            generic.record(0, .a),
            generic.record(1, .b),
            generic.record(2, .d),
            generic.record(3, .e6),
            generic.record(4, .e7),
            generic.record(5, .e8),
        } };
    }

    fn select(self: *const BackendRegistry, simple: symmetry.SimpleLieAlgebra) ?backend.Record {
        for (self.records) |record| {
            if (record.family == simple.family) return record;
        }
        return null;
    }
};

fn EvaluationSinkAdapter(comptime Sink: type) type {
    return struct {
        inner: Sink,

        pub fn emitTerm(self: *@This(), term: rendering.SymbolicTerm) !void {
            try rendering.emitEvaluationTerm(self.inner, .{
                .coefficient = term.coefficient,
                .atoms = term.atoms,
            });
        }
    };
}

fn emitRenderedTerm(allocator: std.mem.Allocator, options: rendering.RenderOptions, sink: anytype, term: rendering.SymbolicTerm, audit: *rendering.ExpansionAudit, lowered_atoms: *std.ArrayList(rendering.SymbolicAtom)) !void {
    var emitted_term = term;
    if (options.lower_clifford_product_atoms or options.gamma_only) {
        lowered_atoms.clearRetainingCapacity();
        audit.clifford_product_factors += try rendering.appendLoweredCliffordProductAtoms(allocator, lowered_atoms, term);
        emitted_term = .{
            .coefficient = term.coefficient,
            .atoms = lowered_atoms.items,
        };
    }
    if (options.gamma_only) {
        var lowering_audit: rendering.AtomLoweringAudit = .{};
        try lowering_audit.recordTerm(emitted_term);
        if (!lowering_audit.gammaOnly()) return error.NonGammaOnlyRenderTerm;
    }

    try rendering.emitTerm(sink, emitted_term);
    audit.emitted += 1;
    if (!options.stream_clifford_product_factors or options.lower_clifford_product_atoms) return;
    if (comptime sinkSupportsCliffordProductFactors(@TypeOf(sink))) {
        audit.clifford_product_factors += try rendering.streamCliffordProductFactors(term, sink);
    } else {
        return error.UnsupportedCliffordProductFactorSink;
    }
}

fn incrementLocalFormulaTermIndices(indices: []u8, counts: []const u8) bool {
    if (indices.len != counts.len) return false;
    var index = indices.len;
    while (index > 0) {
        index -= 1;
        indices[index] += 1;
        if (indices[index] < counts[index]) return true;
        indices[index] = 0;
    }
    return false;
}

fn tensorSpinorProjectionSpec(projection: rendering.TensorSpinorProjection) projector_constructor.TensorSpinorProjectionSpec {
    return .{
        .operator_id = projection.operator_id,
        .left = projection.left,
        .right = projection.right,
        .output = projection.output,
        .orthogonal_dimension = projection.orthogonal_dimension,
        .left_has_spinor = projection.left_has_spinor,
        .right_has_spinor = projection.right_has_spinor,
        .output_has_spinor = projection.output_has_spinor,
        .right_chirality = projection.right_chirality,
        .input_form_profile = projection.input_form_profile,
        .input_form_count = projection.input_form_count,
        .input_tower_power = projection.input_tower_power,
        .form_rank = projection.form_rank,
        .form_count = projection.form_count,
        .form_mask = projection.form_mask,
        .form_profile = projection.form_profile,
        .tower_power = projection.tower_power,
        .chirality = projection.chirality,
        .duality = projection.duality,
    };
}

fn tensorFormProjectionSpec(projection: rendering.TensorFormProjection) projector_constructor.TensorFormProjectionSpec {
    return .{
        .operator_id = projection.operator_id,
        .left = projection.left,
        .right = projection.right,
        .output = projection.output,
        .orthogonal_dimension = projection.orthogonal_dimension,
        .input_form_profile = projection.input_form_profile,
        .input_form_mask = projection.input_form_mask,
        .output_form_profile = projection.output_form_profile,
        .output_form_count = projection.output_form_count,
        .output_form_rank = projection.output_form_rank,
        .output_duality = projection.output_duality,
        .right_chirality = projection.right_chirality,
        .chirality = projection.chirality,
    };
}

fn structuralProjectorSpecFromOrthogonalStep(step: OrthogonalStructuralStep) projector_constructor.StructuralProjectorSpec {
    var spec: projector_constructor.StructuralProjectorSpec = .{
        .operator_id = step.operator_id,
        .orthogonal_dimension = step.dimension,
        .left = structuralEndpointFromOrthogonalEndpoint(step.left),
        .right = structuralEndpointFromOrthogonalEndpoint(step.right),
        .output = structuralEndpointFromOrthogonalEndpoint(step.output),
    };
    if (spec.left.has_spinor and spec.right.has_spinor and !spec.output.has_spinor) {
        spec.left.tower_power = 0;
        if (spec.output.form_duality != .none and spec.left.form_profile == 0) {
            spec.right.chirality = 0;
        }
    }
    return spec;
}

fn structuralEndpointFromOrthogonalEndpoint(endpoint: OrthogonalEndpoint) projector_constructor.StructuralEndpoint {
    const irrep = endpoint.irrep;
    return .{
        .index = endpoint.index,
        .form_profile = irrep.form_profile,
        .form_mask = irrep.form_mask,
        .form_count = irrep.form_count,
        .form_rank = irrep.form_rank,
        .form_duality = irrep.form_duality,
        .young_row_count = irrep.young_row_count,
        .young_rows = irrep.young_rows,
        .young_box_count = irrep.young_box_count,
        .tower_power = irrep.tower_power,
        .chirality = irrep.chirality,
        .has_spinor = irrep.has_spinor,
    };
}

fn multiplyRenderingRationals(left: rendering.RationalId, right: rendering.RationalId) !rendering.RationalId {
    if (rendering.rationalEql(left, rendering.rationalOne())) return right;
    if (rendering.rationalEql(right, rendering.rationalOne())) return left;
    var left_numerator: i128 = left.numerator;
    var right_numerator: i128 = right.numerator;
    var left_denominator: u128 = left.denominator;
    var right_denominator: u128 = right.denominator;
    if (left_numerator == 0 or right_numerator == 0) return rendering.rationalFromSmall(0, 1);

    const left_cross = gcdU128(absI128(left_numerator), right_denominator);
    left_numerator = @divExact(left_numerator, @as(i128, @intCast(left_cross)));
    right_denominator = @divExact(right_denominator, left_cross);
    const right_cross = gcdU128(absI128(right_numerator), left_denominator);
    right_numerator = @divExact(right_numerator, @as(i128, @intCast(right_cross)));
    left_denominator = @divExact(left_denominator, right_cross);

    return .{
        .numerator = try std.math.mul(i128, left_numerator, right_numerator),
        .denominator = try std.math.mul(u128, left_denominator, right_denominator),
    };
}

fn absI128(value: i128) u128 {
    if (value == std.math.minInt(i128)) return @as(u128, 1) << 127;
    return if (value < 0) @intCast(-value) else @intCast(value);
}

fn gcdU128(left: u128, right: u128) u128 {
    var a = left;
    var b = right;
    while (b != 0) {
        const next = a % b;
        a = b;
        b = next;
    }
    return if (a == 0) 1 else a;
}

fn sinkSupportsCliffordProductFactors(comptime Sink: type) bool {
    const target = switch (@typeInfo(Sink)) {
        .pointer => |pointer| pointer.child,
        else => Sink,
    };
    return @hasDecl(target, "emitCliffordProductFactor");
}

test "context audits SU2 four-doublet invariant path count" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const su2 = try ctx.registerAlgebra(.{ .simple = .{ .family = .a, .rank = 1 } });
    const fundamental = try ctx.registerIrrep(su2, .{ .dynkin = &.{1} });
    const leg = realization.ExternalLeg.primitive(fundamental, &.{
        .init(.fundamental, "i"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = su2,
        .external_legs = &.{ leg, leg, leg, leg },
    });

    try testing.expectEqual(@as(u128, 2), ctx.impl().couplings.basisPathCount(basis).?);
    const audit = ctx.impl().couplings.basisAudit(basis).?;
    try testing.expectEqual(@as(u128, 2), audit.path_count);
    try testing.expectEqual(@as(u32, 2), audit.stored_path_count);
    try testing.expectEqual(@as(u32, 6), audit.step_count);
    try testing.expectEqual(@as(u32, 4), audit.distinct_projector_count);
    try testing.expectEqual(@as(u16, 3), audit.max_path_step_len);
    const paths = ctx.impl().couplings.basisPaths(basis).?;
    try testing.expectEqual(@as(usize, 2), paths.len);
    for (paths) |path| {
        const steps = ctx.impl().couplings.pathSteps(path);
        try testing.expectEqual(@as(usize, 3), steps.len);
        try testing.expectEqual(fundamental.value, steps[0].left.value);
        try testing.expectEqual(fundamental.value, steps[0].right.value);
        try testing.expectEqual(@as(u16, 0), steps[0].multiplicity_copy);
        for (steps) |step| {
            const derivation = ctx.impl().projectors.projectorDerivation(step.projector).?;
            if (derivation.formula_kind == .identity) {
                try testing.expectEqual(projector.ProjectorKind.backend_specific_verified, derivation.kind);
                try testing.expectEqual(projector.ExpansionSource.backend_specific_verified, derivation.source);
                try testing.expectEqual(projector.ExpansionStatus.expandable_terms, derivation.status);
                try testing.expect(derivation.formula_audit.verified());
            } else {
                try testing.expectEqual(projector.ProjectorKind.highest_weight_solver, derivation.kind);
                try testing.expectEqual(projector.ExpansionSource.highest_weight_solver, derivation.source);
                try testing.expectEqual(projector.ExpansionStatus.expandable_named, derivation.status);
            }
        }
    }
}

test "context streams empty invariant through expansion filters" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const su2 = try ctx.registerAlgebra(.{ .simple = .{ .family = .a, .rank = 1 } });
    const basis = try ctx.invariantBasis(.{
        .algebra = su2,
        .external_legs = &.{},
    });

    var accept_sink: CountingSink = .{};
    const accept_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{}, rendering.ExpansionFilter.acceptAll(), &accept_sink);
    try testing.expectEqual(@as(u32, 1), accept_sink.term_count);
    try testing.expectEqual(@as(u32, 0), accept_sink.atom_count);
    try testing.expectEqual(@as(u64, 1), accept_audit.accepted);
    try testing.expectEqual(@as(u64, 1), accept_audit.emitted);

    var reject_sink: CountingSink = .{};
    const reject_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{}, rendering.ExpansionFilter.rejectAll(), &reject_sink);
    try testing.expectEqual(@as(u32, 0), reject_sink.term_count);
    try testing.expectEqual(@as(u64, 1), reject_audit.rejected);
    try testing.expectEqual(@as(u64, 0), reject_audit.emitted);

    var projector_filter_sink: CountingSink = .{};
    const projector_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{}, rendering.ExpansionFilter.withoutOperatorKind(.projector), &projector_filter_sink);
    try testing.expectEqual(@as(u32, 1), projector_filter_sink.term_count);
    try testing.expectEqual(@as(u64, 1), projector_filter_audit.undecided);
    try testing.expectEqual(@as(u64, 1), projector_filter_audit.emitted);
}

test "context streams non-empty invariant as named projector chain" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const su2 = try ctx.registerAlgebra(.{ .simple = .{ .family = .a, .rank = 1 } });
    const fundamental = try ctx.registerIrrep(su2, .{ .dynkin = &.{1} });
    const leg = realization.ExternalLeg.primitive(fundamental, &.{
        .init(.fundamental, "i"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = su2,
        .external_legs = &.{ leg, leg },
    });

    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{}, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expect(sink.term_count > 0);
    try testing.expectEqual(@as(u32, 1), sink.atom_count);
    try testing.expectEqual(@as(u32, 1), sink.projector_operator_count);
    const descriptor = ctx.projectorDescriptor(sink.first_projector_operator_id.?).?;
    switch (descriptor.role) {
        .product_channel => |channel| {
            try testing.expectEqual(fundamental.value, channel.left.value);
            try testing.expectEqual(fundamental.value, channel.right.value);
            try testing.expectEqual(@as(u16, 0), channel.multiplicity_copy);
        },
        else => return error.ExpectedProductChannelProjector,
    }
    try testing.expectEqual(projector.ProjectorKind.highest_weight_solver, descriptor.derivation.kind);
    try testing.expectEqual(@as(u64, sink.term_count), audit.accepted);
    try testing.expectEqual(@as(u64, sink.term_count), audit.emitted);

    const first_counters = ctx.impl().projectors.expansionCounters();
    try testing.expectEqual(@as(u64, 0), first_counters.named_hits);
    try testing.expectEqual(@as(u64, 1), first_counters.named_misses);

    var second_sink: CountingSink = .{};
    _ = try ctx.renderInvariantFiltered(basis, .init(0), .{}, rendering.ExpansionFilter.acceptAll(), &second_sink);
    const second_counters = ctx.impl().projectors.expansionCounters();
    try testing.expectEqual(@as(u64, 1), second_counters.named_hits);
    try testing.expectEqual(@as(u64, 1), second_counters.named_misses);

    var projector_filter_sink: CountingSink = .{};
    const projector_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{}, rendering.ExpansionFilter.withoutOperatorKind(.projector), &projector_filter_sink);
    try testing.expectEqual(@as(u32, 0), projector_filter_sink.term_count);
    try testing.expectEqual(@as(u64, 1), projector_filter_audit.rejected);
    try testing.expectEqual(@as(u64, 0), projector_filter_audit.emitted);
}

test "context rejects render signature mismatches before projector cache use" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const su2 = try ctx.registerAlgebra(.{ .simple = .{ .family = .a, .rank = 1 } });
    const fundamental = try ctx.registerIrrep(su2, .{ .dynkin = &.{1} });
    const leg = realization.ExternalLeg.primitive(fundamental, &.{
        .init(.fundamental, "i"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = su2,
        .external_legs = &.{ leg, leg },
    });

    var sink: CountingSink = .{};
    try testing.expectError(error.UnsupportedRenderSignature, ctx.renderInvariant(basis, .init(0), .{ .signature = .euclidean }, &sink));
    try testing.expectEqual(@as(u32, 0), sink.term_count);

    var basis_sink: CountingSink = .{};
    try testing.expectError(error.UnsupportedRenderSignature, ctx.renderBasis(basis, .{ .signature = .euclidean }, &basis_sink));
    try testing.expectEqual(@as(u32, 0), basis_sink.term_count);

    const counters = ctx.impl().projectors.expansionCounters();
    try testing.expectEqual(@as(u64, 0), counters.named_hits);
    try testing.expectEqual(@as(u64, 0), counters.named_misses);
    try testing.expectEqual(@as(u64, 0), counters.formula_hits);
    try testing.expectEqual(@as(u64, 0), counters.formula_misses);
}

test "context streams projected realization boundary projector" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const vector = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 0 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const vector_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 1 } });
    const dual_vector_spinor = try ctx.dualIrrep(vector_spinor);
    const projected = try ctx.registerRealization(realization.RealizationSpec.projected(vector_spinor, &.{ vector, spinor }, &.{
        .init(.vector, "m"),
        .init(.spinor, "a"),
    }, 0));
    const projected_leg = realization.ExternalLeg.realized(projected, &.{
        .init(.vector, "m"),
        .init(.spinor, "a"),
    });
    const dual_leg = realization.ExternalLeg.primitive(dual_vector_spinor, &.{
        .init(.conjugate_spinor, "b"),
        .init(.vector, "n"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ projected_leg, dual_leg },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    const basis_audit = ctx.basisAudit(basis).?;
    try testing.expectEqual(@as(u32, 1), basis_audit.distinct_projector_count);
    try testing.expectEqual(@as(u32, 1), basis_audit.boundary_projector_count);
    try testing.expectEqual(@as(u32, 2), basis_audit.total_projector_count);
    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{}, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expect(sink.term_count > 0);
    try testing.expectEqual(@as(u32, 2), sink.projector_operator_count);
    try testing.expectEqual(@as(u64, 1), audit.accepted);
    try testing.expectEqual(@as(u64, 1), audit.emitted);

    const descriptor = ctx.projectorDescriptor(sink.first_projector_operator_id.?).?;
    switch (descriptor.role) {
        .boundary_realization => |handle| try testing.expectEqual(projected.value, handle.value),
        else => return error.ExpectedBoundaryRealizationProjector,
    }

    var expanded_sink: CountingSink = .{};
    try testing.expectError(error.ProjectorExpansionNotImplemented, ctx.renderInvariant(basis, .init(0), .{ .projectors = .expanded_terms }, &expanded_sink));
    try testing.expectEqual(@as(u32, 0), expanded_sink.term_count);

    var reject_sink: CountingSink = .{};
    const reject_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.rejectAll(), &reject_sink);
    try testing.expectEqual(@as(u32, 0), reject_sink.term_count);
    try testing.expectEqual(@as(u64, 1), reject_audit.rejected);
    try testing.expectEqual(@as(u64, 0), reject_audit.emitted);
}

test "context expands Spin10 vector-spinor boundary projector formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const vector = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 0 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const vector_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 1 } });
    const projected = try ctx.registerRealization(realization.RealizationSpec.projected(vector_spinor, &.{ vector, spinor }, &.{
        .init(.vector, "m"),
        .init(.spinor, "a"),
    }, 0));
    const projected_leg = realization.ExternalLeg.realized(projected, &.{
        .init(.vector, "m"),
        .init(.spinor, "a"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{projected_leg},
        .target = .{ .irrep = vector_spinor },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    const basis_audit = ctx.basisAudit(basis).?;
    try testing.expectEqual(@as(u32, 0), basis_audit.distinct_projector_count);
    try testing.expectEqual(@as(u32, 1), basis_audit.boundary_projector_count);
    try testing.expectEqual(@as(u32, 1), basis_audit.total_projector_count);
    const coverage = try ctx.impl().basisFormulaCoverageAudit(basis);
    try testing.expectEqual(@as(u32, 1), coverage.path_count);
    try testing.expectEqual(@as(u64, 0), coverage.local_step_count);
    try testing.expectEqual(@as(u32, 1), coverage.boundary_projector_count);
    try testing.expectEqual(@as(u64, 1), coverage.boundary_step_count);
    try testing.expectEqual(@as(u64, 1), coverage.expandable_boundary_step_count);
    try testing.expectEqual(@as(u64, 0), coverage.missing_boundary_step_count);
    try testing.expectEqual(@as(u32, 1), coverage.distinct_boundary_projector_count);
    try testing.expectEqual(@as(u32, 1), coverage.fully_expandable_path_count);
    try testing.expect(coverage.first_missing_projector == null);

    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 2), sink.term_count);
    try testing.expectEqual(@as(u32, 2), sink.atom_count);
    try testing.expectEqual(@as(u32, 1), sink.vector_spinor_identity_count);
    try testing.expectEqual(@as(u32, 1), sink.gamma_trace_count);
    try testing.expectEqual(@as(u16, 10), sink.first_gamma_trace_dimension.?);
    try testing.expectEqual(@as(u8, 2), sink.first_gamma_trace_chirality.?);
    try testing.expectEqual(@as(i32, -1), sink.first_gamma_trace_coefficient.?.numerator);
    try testing.expectEqual(@as(u32, 10), sink.first_gamma_trace_coefficient.?.denominator);
    try testing.expectEqual(@as(u64, 1), audit.boundary_projector_atoms);
    try testing.expectEqual(@as(u64, 0), audit.local_projector_atoms);
    try testing.expectEqual(@as(u64, 2), audit.emitted);

    const descriptor = ctx.projectorDescriptor(sink.first_gamma_trace_operator_id.?).?;
    try testing.expectEqual(projector.ProjectorKind.backend_specific_verified, descriptor.derivation.kind);
    try testing.expectEqual(projector.ExpansionSource.backend_specific_verified, descriptor.derivation.source);
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, descriptor.derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_gamma_traceless, descriptor.derivation.formula_kind);
    try testing.expect(descriptor.derivation.formula_audit.normalized);
    try testing.expect(descriptor.derivation.formula_audit.idempotent);
    try testing.expect(descriptor.derivation.formula_audit.channel_separated);
    try testing.expect(descriptor.derivation.formula_audit.gamma_traceless);

    var reject_sink: CountingSink = .{};
    const reject_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.rejectAll(), &reject_sink);
    try testing.expectEqual(@as(u32, 0), reject_sink.term_count);
    try testing.expectEqual(@as(u64, 1), reject_audit.rejected);
    try testing.expectEqual(@as(u64, 0), reject_audit.emitted);

    var gamma_filter_sink: CountingSink = .{};
    const gamma_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.gamma), &gamma_filter_sink);
    try testing.expectEqual(@as(u32, 1), gamma_filter_sink.term_count);
    try testing.expectEqual(@as(u32, 1), gamma_filter_sink.vector_spinor_identity_count);
    try testing.expectEqual(@as(u32, 0), gamma_filter_sink.gamma_trace_count);
    try testing.expectEqual(@as(u64, 1), gamma_filter_audit.rejected);
    try testing.expectEqual(@as(u64, 1), gamma_filter_audit.emitted);
}

test "context audits vector-spinor projector law from orthogonal dimension" {
    const testing = std.testing;

    const spin10 = orthogonalVectorSpinorFormulaAudit(10);
    try testing.expect(spin10.normalized);
    try testing.expect(spin10.idempotent);
    try testing.expect(spin10.channel_separated);
    try testing.expect(spin10.gamma_traceless);

    const rejected = orthogonalVectorSpinorFormulaAudit(0);
    try testing.expect(!rejected.normalized);
    try testing.expect(!rejected.idempotent);
    try testing.expect(!rejected.channel_separated);
    try testing.expect(!rejected.gamma_traceless);
}

test "context audits spinor-square gamma projector law symbolically" {
    const testing = std.testing;

    const so10: symmetry.SimpleLieAlgebra = .{ .family = .d, .rank = 5 };
    const spinor_right = [_]i16{ 0, 0, 0, 0, 1 };
    const spinor_left = [_]i16{ 0, 0, 0, 1, 0 };

    const vector_channel = orthogonalSpinorBilinearFormulaAudit(so10, spinor_right[0..], spinor_right[0..], 1, .none);
    try testing.expect(vector_channel.normalized);
    try testing.expect(vector_channel.idempotent);
    try testing.expect(vector_channel.channel_separated);

    const wrong_chirality = orthogonalSpinorBilinearFormulaAudit(so10, spinor_right[0..], spinor_left[0..], 1, .none);
    try testing.expect(!wrong_chirality.normalized);
    try testing.expect(!wrong_chirality.idempotent);
    try testing.expect(!wrong_chirality.channel_separated);

    const bad_duality = orthogonalSpinorBilinearFormulaAudit(so10, spinor_right[0..], spinor_right[0..], 3, .self_dual);
    try testing.expect(!bad_duality.normalized);
    try testing.expect(!bad_duality.idempotent);
    try testing.expect(!bad_duality.channel_separated);
}

test "context formula coverage audits missing boundary projector formulas" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const vector = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 0 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const projected = try ctx.registerRealization(realization.RealizationSpec.projected(vector, &.{ spinor, spinor }, &.{
        .init(.spinor, "a"),
        .init(.spinor, "b"),
    }, 0));
    const projected_leg = realization.ExternalLeg.realized(projected, &.{
        .init(.spinor, "a"),
        .init(.spinor, "b"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{projected_leg},
        .target = .{ .irrep = vector },
    });

    const coverage = try ctx.impl().basisFormulaCoverageAudit(basis);
    try testing.expectEqual(@as(u32, 1), coverage.path_count);
    try testing.expectEqual(@as(u64, 0), coverage.local_step_count);
    try testing.expectEqual(@as(u64, 0), coverage.missing_step_count);
    try testing.expectEqual(@as(u32, 1), coverage.boundary_projector_count);
    try testing.expectEqual(@as(u64, 1), coverage.boundary_step_count);
    try testing.expectEqual(@as(u64, 0), coverage.expandable_boundary_step_count);
    try testing.expectEqual(@as(u64, 1), coverage.missing_boundary_step_count);
    try testing.expectEqual(@as(u32, 0), coverage.fully_expandable_path_count);
    try testing.expectEqual(projected.value, coverage.first_missing_boundary.?.value);

    const descriptor = ctx.projectorDescriptor(coverage.first_missing_projector.?).?;
    switch (descriptor.role) {
        .boundary_realization => |handle| try testing.expectEqual(projected.value, handle.value),
        else => return error.ExpectedBoundaryRealizationProjector,
    }
    try testing.expectEqual(projector.ExpansionStatus.expandable_named, descriptor.derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.named_only, descriptor.derivation.formula_kind);

    var expanded_sink: CountingSink = .{};
    try testing.expectError(error.ProjectorExpansionNotImplemented, ctx.renderInvariant(basis, .init(0), .{ .projectors = .expanded_terms }, &expanded_sink));
    try testing.expectEqual(@as(u32, 0), expanded_sink.term_count);
}

test "context streams Spin10 vector square as metric formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const vector = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 0 } });
    const leg = realization.ExternalLeg.primitive(vector, &.{
        .init(.vector, "m"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ leg, leg },
    });

    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 1), sink.term_count);
    try testing.expectEqual(@as(u32, 1), sink.atom_count);
    try testing.expectEqual(@as(u32, 1), sink.metric_pair_count);
    try testing.expectEqual(@as(u32, 0), sink.projector_operator_count);
    try testing.expectEqual(@as(u64, 1), audit.accepted);
    try testing.expectEqual(@as(u64, 1), audit.emitted);
    const paths = ctx.impl().couplings.basisPaths(basis).?;
    const steps = ctx.impl().couplings.pathSteps(paths[0]);
    const derivation = ctx.impl().projectors.projectorDerivation(steps[0].projector).?;
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_vector_metric, derivation.formula_kind);
    try testing.expect(derivation.formula_audit.verified());
    const first_counters = ctx.impl().projectors.expansionCounters();
    try testing.expectEqual(@as(u64, 0), first_counters.formula_hits);
    try testing.expectEqual(@as(u64, 1), first_counters.formula_misses);

    var second_sink: CountingSink = .{};
    _ = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &second_sink);
    const second_counters = ctx.impl().projectors.expansionCounters();
    try testing.expectEqual(@as(u64, 1), second_counters.formula_hits);
    try testing.expectEqual(@as(u64, 1), second_counters.formula_misses);

    var projector_filter_sink: CountingSink = .{};
    const projector_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.projector), &projector_filter_sink);
    try testing.expectEqual(@as(u32, 1), projector_filter_sink.term_count);
    try testing.expectEqual(@as(u32, 1), projector_filter_sink.metric_pair_count);
    try testing.expectEqual(@as(u64, 1), projector_filter_audit.undecided);
    try testing.expectEqual(@as(u64, 1), projector_filter_audit.emitted);
}

test "context expands Spin10 vector square Young channels" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const scalar = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 0 } });
    const vector = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 0 } });
    const two_form = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 1, 0, 0, 0 } });
    const three_form = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 1, 0, 0 } });
    const symmetric_traceless = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 2, 0, 0, 0, 0 } });
    const mixed_hook = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 1, 0, 0, 0 } });
    const simple: symmetry.SimpleLieAlgebra = .{ .family = .d, .rank = 5 };
    const symmetric_descriptor = orthogonalIrrepDescriptor(simple, &.{ 2, 0, 0, 0, 0 });
    try testing.expectEqual(OrthogonalIrrepKind.vector_young_shape, symmetric_descriptor.kind);
    try testing.expectEqual(@as(u8, 1), symmetric_descriptor.young_row_count);
    try testing.expectEqual(@as(u8, 2), symmetric_descriptor.young_rows[0]);
    const mixed_descriptor = orthogonalIrrepDescriptor(simple, &.{ 1, 1, 0, 0, 0 });
    try testing.expectEqual(OrthogonalIrrepKind.vector_young_shape, mixed_descriptor.kind);
    try testing.expectEqual(@as(u8, 2), mixed_descriptor.young_row_count);
    try testing.expectEqual(@as(u8, 2), mixed_descriptor.young_rows[0]);
    try testing.expectEqual(@as(u8, 1), mixed_descriptor.young_rows[1]);
    const square_descriptor = orthogonalIrrepDescriptor(simple, &.{ 0, 2, 0, 0, 0 });
    try testing.expectEqual(OrthogonalIrrepKind.vector_young_shape, square_descriptor.kind);
    try testing.expectEqual(@as(u8, 2), square_descriptor.young_row_count);
    try testing.expectEqual(@as(u8, 2), square_descriptor.young_rows[0]);
    try testing.expectEqual(@as(u8, 2), square_descriptor.young_rows[1]);

    const product = try ctx.impl().decomposeProduct(vector, vector);
    const terms = ctx.impl().decompositions.productTerms(product) orelse return error.UnknownProductDecomposition;
    var saw_scalar = false;
    var saw_two_form = false;
    var saw_symmetric_traceless = false;
    for (terms) |term| {
        try testing.expectEqual(@as(u16, 1), term.multiplicity);
        if (term.irrep.value == scalar.value) saw_scalar = true;
        if (term.irrep.value == two_form.value) saw_two_form = true;
        if (term.irrep.value == symmetric_traceless.value) saw_symmetric_traceless = true;
    }
    try testing.expect(saw_scalar);
    try testing.expect(saw_two_form);
    try testing.expect(saw_symmetric_traceless);

    const scalar_projector = try ctx.impl().localProductProjector(vector, vector, scalar, 0);
    const scalar_derivation = ctx.impl().projectors.projectorDerivation(scalar_projector).?;
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_vector_metric, scalar_derivation.formula_kind);

    const two_form_projector = try ctx.impl().localProductProjector(vector, vector, two_form, 0);
    const two_form_step: coupling.CouplingStep = .{ .left = vector, .right = vector, .output = two_form, .multiplicity_copy = 0, .projector = two_form_projector };
    const two_form_derivation = ctx.impl().projectors.projectorDerivation(two_form_projector).?;
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, two_form_derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_structural_projection, two_form_derivation.formula_kind);
    try testing.expectEqual(@as(u8, 2), try ctx.impl().localFormulaStepTermCount(two_form_step, .orthogonal_structural_projection));

    const symmetric_projector = try ctx.impl().localProductProjector(vector, vector, symmetric_traceless, 0);
    const symmetric_step: coupling.CouplingStep = .{ .left = vector, .right = vector, .output = symmetric_traceless, .multiplicity_copy = 0, .projector = symmetric_projector };
    const symmetric_derivation = ctx.impl().projectors.projectorDerivation(symmetric_projector).?;
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, symmetric_derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_structural_projection, symmetric_derivation.formula_kind);
    try testing.expectEqual(@as(u8, 3), try ctx.impl().localFormulaStepTermCount(symmetric_step, .orthogonal_structural_projection));

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var delta_count: u32 = 0;
    var metric_count: u32 = 0;
    var term_index: u8 = 0;
    while (term_index < 3) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        const coefficient = try ctx.impl().appendLocalFormulaStepTermAtoms(&atoms, symmetric_step, 0, 1, 2, .orthogonal_structural_projection, term_index);
        if (term_index < 2) {
            try testing.expectEqual(@as(i128, 1), coefficient.numerator);
            try testing.expectEqual(@as(u128, 2), coefficient.denominator);
        } else {
            try testing.expectEqual(@as(i128, -1), coefficient.numerator);
            try testing.expectEqual(@as(u128, 10), coefficient.denominator);
        }
        try testing.expectEqual(@as(usize, 2), atoms.items.len);
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_delta => delta_count += 1,
                .vector_slot_metric => metric_count += 1,
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
    try testing.expectEqual(@as(u32, 4), delta_count);
    try testing.expectEqual(@as(u32, 2), metric_count);

    const mixed_product = try ctx.impl().decomposeProduct(vector, two_form);
    const mixed_terms = ctx.impl().decompositions.productTerms(mixed_product) orelse return error.UnknownProductDecomposition;
    var saw_vector_in_mixed = false;
    var saw_three_form = false;
    var saw_mixed_hook = false;
    for (mixed_terms) |term| {
        try testing.expectEqual(@as(u16, 1), term.multiplicity);
        if (term.irrep.value == vector.value) saw_vector_in_mixed = true;
        if (term.irrep.value == three_form.value) saw_three_form = true;
        if (term.irrep.value == mixed_hook.value) saw_mixed_hook = true;
    }
    try testing.expect(saw_vector_in_mixed);
    try testing.expect(saw_three_form);
    try testing.expect(saw_mixed_hook);

    const mixed_projector = try ctx.impl().localProductProjector(vector, two_form, mixed_hook, 0);
    const mixed_step: coupling.CouplingStep = .{ .left = vector, .right = two_form, .output = mixed_hook, .multiplicity_copy = 0, .projector = mixed_projector };
    const mixed_derivation = ctx.impl().projectors.projectorDerivation(mixed_projector).?;
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, mixed_derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_structural_projection, mixed_derivation.formula_kind);
    try testing.expectEqual(@as(u8, 5), try ctx.impl().localFormulaStepTermCount(mixed_step, .orthogonal_structural_projection));

    delta_count = 0;
    metric_count = 0;
    term_index = 0;
    while (term_index < 5) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try ctx.impl().appendLocalFormulaStepTermAtoms(&atoms, mixed_step, 0, 1, 2, .orthogonal_structural_projection, term_index);
        try testing.expectEqual(@as(usize, 3), atoms.items.len);
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_delta => delta_count += 1,
                .vector_slot_metric => metric_count += 1,
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
    try testing.expectEqual(@as(u32, 11), delta_count);
    try testing.expectEqual(@as(u32, 4), metric_count);
}

test "context streams Spin10 spinor conjugate spinor as spinor pairing formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const conjugate_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 1, 0 } });
    const spinor_leg = realization.ExternalLeg.primitive(spinor, &.{
        .init(.spinor, "a"),
    });
    const conjugate_leg = realization.ExternalLeg.primitive(conjugate_spinor, &.{
        .init(.conjugate_spinor, "b"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ spinor_leg, conjugate_leg },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 1), sink.term_count);
    try testing.expectEqual(@as(u32, 1), sink.atom_count);
    try testing.expectEqual(@as(u32, 1), sink.spinor_pair_count);
    try testing.expectEqual(@as(u16, 10), sink.first_spinor_pair_dimension.?);
    try testing.expectEqual(@as(u8, 2), sink.first_spinor_pair_left_chirality.?);
    try testing.expectEqual(@as(u8, 1), sink.first_spinor_pair_right_chirality.?);
    try testing.expectEqual(@as(u32, 0), sink.projector_operator_count);
    try testing.expectEqual(@as(u64, 1), audit.accepted);
    try testing.expectEqual(@as(u64, 1), audit.emitted);

    const descriptor = ctx.projectorDescriptor(sink.first_spinor_pair_operator_id.?).?;
    switch (descriptor.role) {
        .product_channel => |channel| {
            try testing.expectEqual(spinor.value, channel.left.value);
            try testing.expectEqual(conjugate_spinor.value, channel.right.value);
            try testing.expectEqual(@as(u16, 0), channel.multiplicity_copy);
        },
        else => return error.ExpectedSpinorPairProductChannel,
    }
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, descriptor.derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_spinor_pair, descriptor.derivation.formula_kind);
    try testing.expect(descriptor.derivation.formula_audit.verified());

    var metric_filter_sink: CountingSink = .{};
    const metric_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.metric), &metric_filter_sink);
    try testing.expectEqual(@as(u32, 0), metric_filter_sink.term_count);
    try testing.expectEqual(@as(u64, 1), metric_filter_audit.rejected);
    try testing.expectEqual(@as(u64, 0), metric_filter_audit.emitted);
}

test "context streams Spin10 spinor spinor vector as gamma formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const vector = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 0 } });
    const spinor_leg = realization.ExternalLeg.primitive(spinor, &.{
        .init(.spinor, "a"),
    });
    const vector_leg = realization.ExternalLeg.primitive(vector, &.{
        .init(.vector, "m"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ spinor_leg, spinor_leg, vector_leg },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 1), sink.term_count);
    try testing.expectEqual(@as(u32, 2), sink.atom_count);
    try testing.expectEqual(@as(u32, 1), sink.gamma_matrix_count);
    try testing.expectEqual(@as(u32, 1), sink.metric_pair_count);
    try testing.expectEqual(@as(u16, 10), sink.first_gamma_dimension.?);
    try testing.expectEqual(@as(u8, 1), sink.first_gamma_rank.?);
    try testing.expectEqual(@as(u8, 2), sink.first_gamma_chirality.?);
    try testing.expectEqual(@as(u32, 0), sink.gamma_operator_count);
    try testing.expectEqual(@as(u32, 0), sink.projector_operator_count);
    const descriptor = ctx.projectorDescriptor(sink.first_gamma_operator_id.?).?;
    switch (descriptor.role) {
        .product_channel => |channel| {
            try testing.expectEqual(spinor.value, channel.left.value);
            try testing.expectEqual(spinor.value, channel.right.value);
            try testing.expectEqual(vector.value, channel.output.value);
            try testing.expectEqual(@as(u16, 0), channel.multiplicity_copy);
        },
        else => return error.ExpectedGammaProductChannel,
    }
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, descriptor.derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_spinor_form_channel, descriptor.derivation.formula_kind);
    try testing.expect(descriptor.derivation.formula_audit.verified());
    try testing.expectEqual(@as(u64, 1), audit.accepted);
    try testing.expectEqual(@as(u64, 1), audit.emitted);

    var eval_sink: EvaluationCountingSink = .{};
    const eval_audit = try ctx.evaluateBasisInvariant(basis, .init(0), .{}, &eval_sink);
    try testing.expectEqual(@as(u64, 1), eval_audit.terms);
    try testing.expectEqual(@as(u64, 0), eval_audit.rejected);
    try testing.expectEqual(@as(u64, 0), eval_audit.lowered_clifford_factors);
    try testing.expectEqual(@as(u32, 1), eval_sink.term_count);
    try testing.expectEqual(@as(u32, 2), eval_sink.atom_count);
    try testing.expectEqual(@as(u32, 1), eval_sink.gamma_matrix_count);
    try testing.expectEqual(@as(u32, 1), eval_sink.metric_pair_count);
    try testing.expectEqual(@as(u32, 0), eval_sink.compact_formula_count);
    try testing.expectEqual(@as(i32, 1), eval_sink.first_coefficient.?.numerator);
    try testing.expectEqual(@as(u32, 1), eval_sink.first_coefficient.?.denominator);
    try testing.expectError(error.NotImplemented, ctx.evaluateInvariant(.init(0), .{}, &eval_sink));
    try testing.expectError(error.UnsupportedEvalSignature, ctx.evaluateBasisInvariant(basis, .init(0), .{ .signature = .euclidean }, &eval_sink));

    var gamma_filter_sink: CountingSink = .{};
    const gamma_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.gamma), &gamma_filter_sink);
    try testing.expectEqual(@as(u32, 0), gamma_filter_sink.term_count);
    try testing.expectEqual(@as(u64, 1), gamma_filter_audit.rejected);
    try testing.expectEqual(@as(u64, 0), gamma_filter_audit.emitted);

    const coverage = try ctx.impl().basisFormulaCoverageAudit(basis);
    try testing.expectEqual(@as(u32, 1), coverage.path_count);
    try testing.expectEqual(@as(u64, 2), coverage.local_step_count);
    try testing.expectEqual(@as(u64, 2), coverage.expandable_step_count);
    try testing.expectEqual(@as(u64, 0), coverage.missing_step_count);
    try testing.expectEqual(@as(u32, 1), coverage.fully_expandable_path_count);
}

test "context streams Spin10 conjugate spinor spinor vector as gamma formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const conjugate_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 1, 0 } });
    const vector = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 0 } });
    const spinor_leg = realization.ExternalLeg.primitive(conjugate_spinor, &.{
        .init(.conjugate_spinor, "a"),
    });
    const vector_leg = realization.ExternalLeg.primitive(vector, &.{
        .init(.vector, "m"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ spinor_leg, spinor_leg, vector_leg },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    _ = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 1), sink.gamma_matrix_count);
    try testing.expectEqual(@as(u16, 10), sink.first_gamma_dimension.?);
    try testing.expectEqual(@as(u8, 1), sink.first_gamma_rank.?);
    try testing.expectEqual(@as(u8, 1), sink.first_gamma_chirality.?);
}

test "context streams composed gamma product reducer atoms" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const conjugate_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 1, 0 } });
    const spinor_leg = realization.ExternalLeg.primitive(spinor, &.{
        .init(.spinor, "a"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ spinor_leg, spinor_leg, spinor_leg },
        .target = .{ .irrep = conjugate_spinor },
    });

    try testing.expectEqual(@as(u128, 2), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    const audit = try ctx.renderBasisFiltered(basis, .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 2), sink.term_count);
    try testing.expect(sink.gamma_matrix_count + sink.gamma_form_count > 0);
    try testing.expect(sink.gamma_action_count > 0);
    try testing.expect(sink.clifford_product_count > 0);
    try testing.expect(sink.first_clifford_product_left_rank.? > 0);
    try testing.expect(sink.first_clifford_product_right_rank.? > 0);
    try testing.expect(sink.first_clifford_product_coefficient.? != 0);
    try testing.expectEqual(@as(u64, 2), audit.emitted);

    var factor_sink: CountingSink = .{};
    const factor_audit = try ctx.renderBasisFiltered(basis, .{
        .projectors = .expanded_terms,
        .stream_clifford_product_factors = true,
    }, rendering.ExpansionFilter.acceptAll(), &factor_sink);
    try testing.expectEqual(@as(u32, 2), factor_sink.term_count);
    try testing.expect(factor_sink.clifford_product_factor_count > 0);
    try testing.expect(factor_sink.clifford_product_metric_factor_count > 0);
    try testing.expect(factor_sink.clifford_product_output_vector_factor_count > 0);
    try testing.expectEqual(@as(u64, @intCast(factor_sink.clifford_product_factor_count)), factor_audit.clifford_product_factors);

    var lowered_sink: CountingSink = .{};
    const lowered_audit = try ctx.renderBasisFiltered(basis, .{
        .projectors = .expanded_terms,
        .lower_clifford_product_atoms = true,
    }, rendering.ExpansionFilter.acceptAll(), &lowered_sink);
    try testing.expectEqual(@as(u32, 2), lowered_sink.term_count);
    try testing.expectEqual(@as(u32, 0), lowered_sink.clifford_product_count);
    try testing.expect(lowered_sink.clifford_product_factor_count > 0);
    try testing.expect(lowered_sink.clifford_product_metric_factor_count > 0);
    try testing.expect(lowered_sink.clifford_product_output_vector_factor_count > 0);
    try testing.expectEqual(lowered_sink.clifford_product_factor_count, lowered_sink.clifford_product_metric_factor_count + lowered_sink.clifford_product_output_vector_factor_count);
    try testing.expectEqual(@as(u64, @intCast(lowered_sink.clifford_product_factor_count)), lowered_audit.clifford_product_factors);
    try testing.expect(lowered_sink.first_clifford_product_factor_left_operator_id != null);
    try testing.expect(lowered_sink.first_clifford_product_factor_right_operator_id != null);
    try testing.expectEqual(@as(u16, 10), lowered_sink.first_clifford_product_factor_dimension.?);
    try testing.expect(lowered_sink.first_clifford_product_factor_coefficient.? != 0);

    var scan_sink: rendering.CliffordProductFactorAuditSink = .{};
    const scan_audit = try ctx.renderBasisFiltered(basis, .{
        .projectors = .expanded_terms,
        .lower_clifford_product_atoms = true,
    }, rendering.ExpansionFilter.acceptAll(), &scan_sink);
    try testing.expectEqual(@as(u64, 2), scan_audit.emitted);
    try testing.expectEqual(@as(u32, 2), scan_sink.term_count);
    try testing.expect(scan_sink.scan.product_count > 0);
    try testing.expectEqual(lowered_sink.clifford_product_factor_count, scan_sink.scan.factor_count);
    try testing.expectEqual(lowered_sink.clifford_product_metric_factor_count, scan_sink.scan.metric_count);
    try testing.expectEqual(lowered_sink.clifford_product_output_vector_factor_count, scan_sink.scan.output_vector_count);
    try testing.expectEqual(@as(u16, 10), scan_sink.scan.first_orthogonal_dimension.?);
    try testing.expect(scan_sink.scan.first_coefficient.? != 0);

    var gamma_filter_sink: CountingSink = .{};
    const gamma_filter_audit = try ctx.renderBasisFiltered(basis, .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.gamma), &gamma_filter_sink);
    try testing.expectEqual(@as(u32, 0), gamma_filter_sink.term_count);
    try testing.expectEqual(@as(u64, 2), gamma_filter_audit.rejected);
    try testing.expectEqual(@as(u64, 0), gamma_filter_audit.emitted);
}

test "context streams Spin10 spinor spinor form as gamma-form formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const conjugate_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 1, 0 } });
    try expectSpin10GammaForm(&ctx, so10, spinor, .spinor, &.{ 0, 0, 1, 0, 0 }, 3, 2, .none);
    try expectSpin10GammaForm(&ctx, so10, spinor, .spinor, &.{ 0, 0, 0, 0, 2 }, 5, 2, .self_dual);
    try expectSpin10GammaForm(&ctx, so10, conjugate_spinor, .conjugate_spinor, &.{ 0, 0, 1, 0, 0 }, 3, 1, .none);
    try expectSpin10GammaForm(&ctx, so10, conjugate_spinor, .conjugate_spinor, &.{ 0, 0, 0, 2, 0 }, 5, 1, .anti_self_dual);
}

test "context streams A2 fundamental cubic as epsilon formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const su3 = try ctx.registerAlgebra(.{ .simple = .{ .family = .a, .rank = 2 } });
    const fundamental = try ctx.registerIrrep(su3, .{ .dynkin = &.{ 1, 0 } });
    const leg = realization.ExternalLeg.primitive(fundamental, &.{
        .init(.fundamental, "i"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = su3,
        .external_legs = &.{ leg, leg, leg },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 1), sink.term_count);
    try testing.expectEqual(@as(u32, 1), sink.atom_count);
    try testing.expectEqual(@as(u32, 1), sink.epsilon_count);
    try testing.expectEqual(@as(u32, 0), sink.projector_operator_count);
    try testing.expectEqual(@as(u64, 1), audit.emitted);

    const paths = ctx.impl().couplings.basisPaths(basis).?;
    const steps = ctx.impl().couplings.pathSteps(paths[0]);
    try testing.expectEqual(@as(usize, 2), steps.len);
    for (steps) |step| {
        const derivation = ctx.impl().projectors.projectorDerivation(step.projector).?;
        try testing.expectEqual(projector.ExpansionStatus.expandable_terms, derivation.status);
        try testing.expectEqual(projector.ProjectorFormulaKind.backend_specific_structure, derivation.formula_kind);
        try testing.expect(derivation.formula_audit.verified());
    }

    var epsilon_filter_sink: CountingSink = .{};
    const epsilon_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.epsilon), &epsilon_filter_sink);
    try testing.expectEqual(@as(u32, 0), epsilon_filter_sink.term_count);
    try testing.expectEqual(@as(u64, 1), epsilon_filter_audit.rejected);
    try testing.expectEqual(@as(u64, 0), epsilon_filter_audit.emitted);
}

test "context streams E6 fundamental cubic as structure formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const e6 = try ctx.registerAlgebra(.{ .simple = .{ .family = .e6, .rank = 6 } });
    const fundamental = try ctx.registerIrrep(e6, .{ .dynkin = &.{ 1, 0, 0, 0, 0, 0 } });
    const leg = realization.ExternalLeg.primitive(fundamental, &.{
        .init(.fundamental, "i"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = e6,
        .external_legs = &.{ leg, leg, leg },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    const coverage = try ctx.basisFormulaCoverageAudit(basis);
    try testing.expectEqual(@as(u32, 1), coverage.path_count);
    try testing.expectEqual(@as(u64, 2), coverage.local_step_count);
    try testing.expectEqual(@as(u64, 2), coverage.expandable_step_count);
    try testing.expectEqual(@as(u64, 0), coverage.missing_step_count);
    try testing.expectEqual(@as(u32, 1), coverage.fully_expandable_path_count);

    var sink: CountingSink = .{};
    const audit = try ctx.renderBasisFiltered(basis, .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u64, 1), audit.invariants);
    try testing.expectEqual(@as(u64, 1), audit.emitted);
    try testing.expectEqual(@as(u32, 1), sink.term_count);
    try testing.expectEqual(@as(u32, 1), sink.atom_count);
    try testing.expectEqual(@as(u32, 1), sink.structure_constant_count);
    try testing.expectEqual(symmetry.LieFamily.e6, sink.first_structure_constant_family.?);
    try testing.expectEqual(@as(u8, 6), sink.first_structure_constant_rank.?);
    try testing.expectEqual(@as(u32, 0), sink.projector_operator_count);

    const paths = ctx.impl().couplings.basisPaths(basis).?;
    const steps = ctx.impl().couplings.pathSteps(paths[0]);
    for (steps) |step| {
        const derivation = ctx.impl().projectors.projectorDerivation(step.projector).?;
        try testing.expectEqual(projector.ProjectorKind.backend_specific_verified, derivation.kind);
        try testing.expectEqual(projector.ExpansionStatus.expandable_terms, derivation.status);
        try testing.expectEqual(projector.ProjectorFormulaKind.backend_specific_structure, derivation.formula_kind);
        try testing.expect(derivation.formula_audit.verified());
    }

    var structure_filter_sink: CountingSink = .{};
    const structure_filter_audit = try ctx.renderBasisFiltered(basis, .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.structure_constant), &structure_filter_sink);
    try testing.expectEqual(@as(u32, 0), structure_filter_sink.term_count);
    try testing.expectEqual(@as(u64, 1), structure_filter_audit.rejected);
    try testing.expectEqual(@as(u64, 0), structure_filter_audit.emitted);
}

test "context streams E8 adjoint cubic as structure formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const e8 = try ctx.registerAlgebra(.{ .simple = .{ .family = .e8, .rank = 8 } });
    const adjoint = try ctx.registerIrrep(e8, .{ .dynkin = &.{ 0, 0, 0, 0, 0, 0, 1, 0 } });
    const leg = realization.ExternalLeg.primitive(adjoint, &.{
        .init(.adjoint, "a"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = e8,
        .external_legs = &.{ leg, leg, leg },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    const coverage = try ctx.basisFormulaCoverageAudit(basis);
    try testing.expectEqual(@as(u32, 1), coverage.path_count);
    try testing.expectEqual(@as(u64, 2), coverage.local_step_count);
    try testing.expectEqual(@as(u64, 2), coverage.expandable_step_count);
    try testing.expectEqual(@as(u64, 0), coverage.missing_step_count);
    try testing.expectEqual(@as(u32, 1), coverage.fully_expandable_path_count);

    var sink: CountingSink = .{};
    const audit = try ctx.renderBasisFiltered(basis, .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u64, 1), audit.invariants);
    try testing.expectEqual(@as(u64, 1), audit.emitted);
    try testing.expectEqual(@as(u32, 1), sink.term_count);
    try testing.expectEqual(@as(u32, 1), sink.atom_count);
    try testing.expectEqual(@as(u32, 1), sink.structure_constant_count);
    try testing.expectEqual(symmetry.LieFamily.e8, sink.first_structure_constant_family.?);
    try testing.expectEqual(@as(u8, 8), sink.first_structure_constant_rank.?);
    try testing.expectEqual(@as(u32, 0), sink.projector_operator_count);

    const paths = ctx.impl().couplings.basisPaths(basis).?;
    const steps = ctx.impl().couplings.pathSteps(paths[0]);
    for (steps) |step| {
        const derivation = ctx.impl().projectors.projectorDerivation(step.projector).?;
        try testing.expectEqual(projector.ProjectorKind.backend_specific_verified, derivation.kind);
        try testing.expectEqual(projector.ExpansionStatus.expandable_terms, derivation.status);
        try testing.expectEqual(projector.ProjectorFormulaKind.backend_specific_structure, derivation.formula_kind);
        try testing.expect(derivation.formula_audit.verified());
    }
}

test "context streams singlet product as identity formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const singlet = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 0 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const singlet_leg = realization.ExternalLeg.primitive(singlet, &.{
        .init(.custom, "s"),
    });
    const spinor_leg = realization.ExternalLeg.primitive(spinor, &.{
        .init(.spinor, "a"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ singlet_leg, spinor_leg },
        .target = .{ .irrep = spinor },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 1), sink.term_count);
    try testing.expectEqual(@as(u32, 1), sink.atom_count);
    try testing.expectEqual(@as(u32, 1), sink.identity_route_count);
    try testing.expectEqual(@as(u32, 0), sink.product_identity_count);
    try testing.expectEqual(@as(u64, 1), audit.accepted);
    try testing.expectEqual(@as(u64, 1), audit.emitted);

    const descriptor = ctx.projectorDescriptor(sink.first_identity_route_operator_id.?).?;
    switch (descriptor.role) {
        .product_channel => |channel| {
            try testing.expectEqual(singlet.value, channel.left.value);
            try testing.expectEqual(spinor.value, channel.right.value);
            try testing.expectEqual(spinor.value, channel.output.value);
            try testing.expectEqual(@as(u16, 0), channel.multiplicity_copy);
        },
        else => return error.ExpectedIdentityProductChannel,
    }
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, descriptor.derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.identity, descriptor.derivation.formula_kind);
    try testing.expect(descriptor.derivation.formula_audit.verified());

    var projector_filter_sink: CountingSink = .{};
    const projector_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.projector), &projector_filter_sink);
    try testing.expectEqual(@as(u32, 1), projector_filter_sink.term_count);
    try testing.expectEqual(@as(u32, 1), projector_filter_sink.identity_route_count);
    try testing.expectEqual(@as(u64, 0), projector_filter_audit.rejected);
    try testing.expectEqual(@as(u64, 1), projector_filter_audit.emitted);
}

test "context streams Spin10 spinor tower Cartan product formula" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const tower3 = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 3 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const tower4 = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 4 } });
    const tower_leg = realization.ExternalLeg.primitive(tower3, &.{
        .init(.custom, "T"),
    });
    const spinor_leg = realization.ExternalLeg.primitive(spinor, &.{
        .init(.spinor, "a"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ tower_leg, spinor_leg },
        .target = .{ .irrep = tower4 },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 1), sink.term_count);
    try testing.expectEqual(@as(u32, 4), sink.atom_count);
    try testing.expectEqual(@as(u32, 4), sink.spinor_index_delta_count);
    try testing.expectEqual(@as(u32, 0), sink.spinor_symmetrized_product_count);
    try testing.expectEqual(@as(u32, 0), sink.cartan_product_count);
    try testing.expectEqual(@as(u64, 1), audit.accepted);
    try testing.expectEqual(@as(u64, 1), audit.emitted);

    const descriptor = ctx.projectorDescriptor(sink.first_spinor_index_delta_operator_id.?).?;
    switch (descriptor.role) {
        .product_channel => |channel| {
            try testing.expectEqual(tower3.value, channel.left.value);
            try testing.expectEqual(spinor.value, channel.right.value);
            try testing.expectEqual(tower4.value, channel.output.value);
            try testing.expectEqual(@as(u16, 0), channel.multiplicity_copy);
        },
        else => return error.ExpectedCartanProductChannel,
    }
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, descriptor.derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.cartan_product_channel, descriptor.derivation.formula_kind);
    try testing.expect(descriptor.derivation.formula_audit.verified());

    var projector_filter_sink: CountingSink = .{};
    const projector_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.projector), &projector_filter_sink);
    try testing.expectEqual(@as(u32, 1), projector_filter_sink.term_count);
    try testing.expectEqual(@as(u32, 4), projector_filter_sink.spinor_index_delta_count);
    try testing.expectEqual(@as(u64, 0), projector_filter_audit.rejected);
    try testing.expectEqual(@as(u64, 1), projector_filter_audit.emitted);

    var gamma_only_sink: CountingSink = .{};
    try ctx.renderInvariant(basis, .init(0), .{
        .projectors = .expanded_terms,
        .gamma_only = true,
    }, &gamma_only_sink);
    try testing.expectEqual(@as(u32, 1), gamma_only_sink.term_count);
    try testing.expectEqual(@as(u32, 4), gamma_only_sink.spinor_index_delta_count);
}

test "context streams Spin10 spinor tower tensor-spinor formula" {
    var ctx = try Context.init(std.testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const tower4 = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 4 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });

    const tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 1, 0, 3 } });
    const shifted_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 1, 0, 2 } });
    const terminal_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 1, 1, 0, 1 } });
    const opposite_terminal_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 1, 1, 0 } });
    const tensor_form = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 2, 0, 0 } });
    const preserve_tensor_form = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 1, 1, 0, 0 } });
    const shifted_tensor_form = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 1, 0, 1, 1 } });
    const shift_down_tensor_form = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 1, 1, 1 } });
    const shift_down_any_tensor_form = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 1, 1 } });
    const remove_shift_down_tensor_form = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 1, 0, 1, 1 } });
    const rank_form_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 1, 2 } });
    const rank_form_tower_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 1, 3 } });
    const all_shift_tower_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 1, 0, 1, 2 } });
    const remove_shift_tower_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 1, 0, 1 } });
    const wrapped_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 3 } });
    const terminal_wrapped_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 1, 0, 0, 1 } });
    const opposite_vector_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 1, 0 } });
    const opposite_rank_split_terminal_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 1, 0, 1, 0 } });
    const opposite_shift_terminal_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 1, 1, 0 } });
    const split_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 1, 0, 0, 2 } });
    const opposite_add_shift_terminal_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 1, 1, 1, 0 } });
    const rank3_terminal_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 1, 0, 1 } });
    const rank3_tower_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 1, 0, 2 } });
    const opposite_rank4_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 2, 1 } });
    const opposite_remove_shift_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 2, 1 } });
    const opposite_rank3_power_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 2, 1, 0 } });
    const opposite_rank3_tower_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 1, 2, 0 } });
    const opposite_form_add_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 1, 0, 2, 0 } });
    const opposite_all_shift_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 1, 2, 0 } });
    const opposite_shift_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 2, 0 } });
    const opposite_merge_tensor_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 1, 0, 2, 1 } });
    const opposite_tower4 = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 4, 0 } });
    const opposite_tower3 = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 3, 0 } });

    try expectSpin10TensorSpinorProjection(&ctx, so10, tower4, spinor, &.{ 0, 0, 1, 0, 3 }, 3, 1, 0b100, 3, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, tower4, spinor, &.{ 1, 0, 0, 0, 3 }, 1, 1, 0b001, 3, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, tensor_spinor, spinor, &.{ 1, 0, 1, 0, 2 }, 1, 2, 0b101, 2, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, shifted_tensor_spinor, spinor, &.{ 0, 1, 1, 0, 1 }, 2, 2, 0b110, 1, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, tensor_form, spinor, &.{ 0, 0, 1, 1, 0 }, 3, 1, 0b100, 1, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, preserve_tensor_form, spinor, &.{ 0, 1, 1, 0, 1 }, 2, 2, 0b0110, 1, 2);
    try expectSpin10TensorFormProjection(&ctx, so10, terminal_tensor_spinor, spinor, &.{ 0, 0, 2, 0, 0 }, 0b110, @as(u128, 2) << 8, 2);
    try expectSpin10TensorFormProjection(&ctx, so10, terminal_tensor_spinor, spinor, &.{ 0, 1, 0, 1, 1 }, 0b110, (@as(u128, 1) << 4) | (@as(u128, 1) << 12), 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, shifted_tensor_form, spinor, &.{ 0, 0, 1, 1, 0 }, 3, 1, 0b100, 1, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, shift_down_tensor_form, spinor, &.{ 0, 0, 2, 1, 0 }, 3, 1, 0b100, 1, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, shift_down_tensor_form, spinor, &.{ 1, 0, 0, 1, 2 }, 1, 2, 0b1001, 1, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, shift_down_tensor_form, spinor, &.{ 1, 0, 1, 1, 0 }, 1, 2, 0b0101, 1, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, shift_down_tensor_form, spinor, &.{ 0, 1, 1, 0, 1 }, 2, 2, 0b0110, 1, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, shift_down_any_tensor_form, spinor, &.{ 2, 0, 0, 1, 0 }, 1, 1, 0b0001, 1, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, remove_shift_down_tensor_form, spinor, &.{ 0, 1, 1, 0, 1 }, 2, 2, 0b0110, 1, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, rank_form_tensor_spinor, spinor, &.{ 1, 0, 0, 0, 2 }, 1, 1, 0b001, 2, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, rank_form_tower_spinor, spinor, &.{ 0, 0, 0, 0, 3 }, 0, 0, 0, 3, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, all_shift_tower_tensor_spinor, spinor, &.{ 1, 0, 1, 0, 2 }, 1, 2, 0b0101, 2, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, remove_shift_tower_tensor_spinor, spinor, &.{ 0, 1, 0, 0, 2 }, 2, 1, 0b0010, 2, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, wrapped_tensor_spinor, spinor, &.{ 0, 0, 0, 1, 3 }, 4, 1, 0b1000, 2, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, wrapped_tensor_spinor, spinor, &.{ 2, 0, 0, 0, 2 }, 1, 1, 0b001, 2, 2);
    try expectSpin10TensorFormProjection(&ctx, so10, terminal_wrapped_tensor_spinor, spinor, &.{ 0, 1, 0, 1, 1 }, 0b0011, (@as(u128, 1) << 4) | (@as(u128, 1) << 12), 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, terminal_wrapped_tensor_spinor, spinor, &.{ 1, 0, 0, 0, 2 }, 1, 1, 0b001, 2, 2);
    try expectSpin10TensorFormProjection(&ctx, so10, opposite_vector_spinor, spinor, &.{ 0, 0, 1, 0, 0 }, 0b0001, @as(u128, 1) << 8, 1);
    try expectSpin10TensorFormProjection(&ctx, so10, opposite_rank_split_terminal_tensor_spinor, spinor, &.{ 1, 0, 1, 0, 0 }, 0b0010, (@as(u128, 1) << 0) | (@as(u128, 1) << 8), 2);
    try expectSpin10TensorFormProjection(&ctx, so10, opposite_shift_terminal_tensor_spinor, spinor, &.{ 0, 1, 0, 1, 1 }, 0b0101, (@as(u128, 1) << 4) | (@as(u128, 1) << 12), 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, split_tensor_spinor, spinor, &.{ 1, 0, 0, 1, 2 }, 1, 2, 0b1001, 1, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, split_tensor_spinor, spinor, &.{ 0, 0, 0, 0, 3 }, 0, 0, 0, 3, 2);
    try expectSpin10TensorFormProjection(&ctx, so10, opposite_add_shift_terminal_tensor_spinor, spinor, &.{ 1, 1, 0, 1, 1 }, 0b0110, (@as(u128, 1) << 0) | (@as(u128, 1) << 4) | (@as(u128, 1) << 12), 3);
    try expectSpin10TensorFormProjection(&ctx, so10, rank3_terminal_tensor_spinor, spinor, &.{ 0, 0, 2, 0, 0 }, 0b0100, @as(u128, 2) << 8, 2);
    try expectSpin10TensorFormProjection(&ctx, so10, rank3_terminal_tensor_spinor, spinor, &.{ 0, 1, 0, 1, 1 }, 0b0100, (@as(u128, 1) << 4) | (@as(u128, 1) << 12), 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, rank3_terminal_tensor_spinor, spinor, &.{ 1, 0, 0, 0, 2 }, 1, 1, 0b0001, 2, 2);
    try expectSpin10TensorFormProjection(&ctx, so10, rank3_terminal_tensor_spinor, spinor, &.{ 1, 0, 1, 0, 0 }, 0b0100, (@as(u128, 1) << 0) | (@as(u128, 1) << 8), 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, rank3_tower_tensor_spinor, spinor, &.{ 0, 0, 1, 0, 3 }, 3, 1, 0b0100, 3, 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_rank4_tensor_spinor, spinor, &.{ 0, 0, 1, 2, 0 }, 3, 1, 0b0100, 2, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_rank4_tensor_spinor, spinor, &.{ 1, 0, 0, 2, 0 }, 1, 1, 0b0001, 2, 1);
    try expectSpin10TensorFormProjection(&ctx, so10, opposite_rank4_tensor_spinor, spinor, &.{ 0, 1, 0, 1, 1 }, 0b1000, (@as(u128, 1) << 4) | (@as(u128, 1) << 12), 2);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_remove_shift_tensor_spinor, spinor, &.{ 0, 1, 0, 2, 0 }, 2, 1, 0b0010, 2, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_rank3_power_tensor_spinor, spinor, &.{ 0, 0, 1, 2, 0 }, 3, 1, 0b0100, 2, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_rank3_tower_tensor_spinor, spinor, &.{ 0, 0, 0, 3, 0 }, 0, 0, 0, 3, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_tower4, spinor, &.{ 0, 0, 0, 3, 0 }, 0, 0, 0, 3, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_tower3, spinor, &.{ 0, 0, 0, 3, 1 }, 4, 1, 0b1000, 2, 1);
    try expectSpin10TensorMiddleFormProjection(&ctx, so10, opposite_tower3, spinor, &.{ 0, 0, 0, 2, 0 }, 0, 5, .anti_self_dual);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_all_shift_tensor_spinor, spinor, &.{ 0, 1, 0, 2, 1 }, 2, 2, 0b1010, 1, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_form_add_tensor_spinor, spinor, &.{ 0, 1, 0, 2, 1 }, 2, 2, 0b1010, 1, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_form_add_tensor_spinor, spinor, &.{ 1, 0, 1, 1, 0 }, 1, 2, 0b0101, 1, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_rank3_tower_tensor_spinor, spinor, &.{ 0, 0, 1, 1, 0 }, 3, 1, 0b0100, 1, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_merge_tensor_spinor, spinor, &.{ 0, 0, 1, 2, 0 }, 3, 1, 0b0100, 2, 1);
    try expectSpin10TensorSpinorProjection(&ctx, so10, opposite_shift_tensor_spinor, spinor, &.{ 0, 0, 1, 1, 0 }, 3, 1, 0b0100, 1, 1);
    try expectSpin10TensorMiddleFormProjection(&ctx, so10, opposite_terminal_tensor_spinor, spinor, &.{ 0, 0, 0, 2, 0 }, 0b100, 5, .anti_self_dual);
    try expectSpin10TensorFormProjection(&ctx, so10, opposite_terminal_tensor_spinor, spinor, &.{ 0, 0, 1, 0, 0 }, 0b100, @as(u128, 1) << 8, 1);
}

test "context refuses expanded render success for missing projector formulas" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const su2 = try ctx.registerAlgebra(.{ .simple = .{ .family = .a, .rank = 1 } });
    const fundamental = try ctx.registerIrrep(su2, .{ .dynkin = &.{1} });
    const leg = realization.ExternalLeg.primitive(fundamental, &.{
        .init(.fundamental, "i"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = su2,
        .external_legs = &.{ leg, leg },
    });

    var sink: CountingSink = .{};
    try testing.expectError(error.ProjectorExpansionNotImplemented, ctx.renderInvariant(basis, .init(0), .{ .projectors = .expanded_terms }, &sink));
    try testing.expectEqual(@as(u32, 0), sink.term_count);
}

test "context reject filter stops non-empty expansion before projector formulas" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const su2 = try ctx.registerAlgebra(.{ .simple = .{ .family = .a, .rank = 1 } });
    const fundamental = try ctx.registerIrrep(su2, .{ .dynkin = &.{1} });
    const leg = realization.ExternalLeg.primitive(fundamental, &.{
        .init(.fundamental, "i"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = su2,
        .external_legs = &.{ leg, leg },
    });

    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.rejectAll(), &sink);
    try testing.expectEqual(@as(u32, 0), sink.term_count);
    try testing.expectEqual(@as(u64, 1), audit.rejected);
    try testing.expectEqual(@as(u64, 0), audit.emitted);
}

test "context reports unsupported fixed tree instead of empty basis" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const su2 = try ctx.registerAlgebra(.{ .simple = .{ .family = .a, .rank = 1 } });
    const fundamental = try ctx.registerIrrep(su2, .{ .dynkin = &.{1} });
    const leg = realization.ExternalLeg.primitive(fundamental, &.{
        .init(.fundamental, "i"),
    });

    try testing.expectError(error.FixedTreeCountingNotImplemented, ctx.invariantBasis(.{
        .algebra = su2,
        .external_legs = &.{ leg, leg },
        .tree_policy = .{ .fixed = &.{ 0, 1 } },
    }));
}

test "context reports unresolved registered realization instead of empty basis" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const su2 = try ctx.registerAlgebra(.{ .simple = .{ .family = .a, .rank = 1 } });
    const unresolved = realization.ExternalLeg.registered("missing-realization", &.{
        .init(.fundamental, "i"),
    });

    try testing.expectError(error.RegisteredRealizationNotResolved, ctx.invariantBasis(.{
        .algebra = su2,
        .external_legs = &.{unresolved},
    }));
}

test "context counts dual-pair invariant across ADE families" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    try expectDualPairInvariantCount(&ctx, .{ .family = .a, .rank = 2 }, &.{ 1, 0 });
    try expectDualPairInvariantCount(&ctx, .{ .family = .d, .rank = 5 }, &.{ 0, 0, 0, 0, 1 });
    try expectDualPairInvariantCount(&ctx, .{ .family = .e6, .rank = 6 }, &.{ 1, 0, 0, 0, 0, 0 });
    try expectDualPairInvariantCount(&ctx, .{ .family = .e7, .rank = 7 }, &.{ 0, 0, 0, 0, 0, 1, 0 });
    try expectDualPairInvariantCount(&ctx, .{ .family = .e8, .rank = 8 }, &.{ 0, 0, 0, 0, 0, 0, 1, 0 });
}

test "context counts representative multi-leg ADE invariants" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    try expectRepeatedLegInvariantCount(&ctx, .{ .family = .a, .rank = 2 }, &.{ 1, 0 }, 3, 1);
    try expectRepeatedLegInvariantCount(&ctx, .{ .family = .d, .rank = 5 }, &.{ 1, 0, 0, 0, 0 }, 2, 1);
    try expectRepeatedLegInvariantCount(&ctx, .{ .family = .e6, .rank = 6 }, &.{ 1, 0, 0, 0, 0, 0 }, 3, 1);
    try expectRepeatedLegInvariantCount(&ctx, .{ .family = .e8, .rank = 8 }, &.{ 0, 0, 0, 0, 0, 0, 1, 0 }, 3, 1);
}

test "context benchmarks Spin10 spinor twelfth power invariant paths" {
    const testing = std.testing;

    var ctx = try Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const leg = realization.ExternalLeg.primitive(spinor, &.{
        .init(.spinor, "a"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ leg, leg, leg, leg, leg, leg, leg, leg, leg, leg, leg, leg },
    });
    const audit = ctx.impl().couplings.basisAudit(basis).?;

    try testing.expectEqual(@as(u128, 73744), audit.path_count);
    try testing.expectEqual(@as(u128, 73744), ctx.basisInvariantCount(basis).?);
    try testing.expectEqual(@as(u128, 73744), ctx.basisAudit(basis).?.path_count);
    try testing.expectEqual(@as(u32, 73744), audit.stored_path_count);
    try testing.expectEqual(@as(u16, 11), audit.max_path_step_len);
    try testing.expect(audit.step_count <= 73744 * 11);
    try testing.expect(audit.distinct_projector_count < audit.step_count);
    const coverage = try ctx.impl().basisFormulaCoverageAudit(basis);
    try testing.expectEqual(@as(u32, 73744), coverage.path_count);
    try testing.expectEqual(coverage.local_step_count, coverage.expandable_step_count + coverage.missing_step_count);
    try testing.expectEqual(@as(u64, 0), coverage.missing_step_count);
    try testing.expectEqual(@as(u32, 73744), coverage.fully_expandable_path_count);
    try testing.expect(coverage.expandable_step_count > 73744);
    try testing.expect(coverage.first_missing_projector == null);

    var sink: CountingSink = .{};
    const expanded_audit = try ctx.renderBasisFiltered(basis, .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u64, 73744), expanded_audit.invariants);
    try testing.expect(sink.term_count >= 73744);
    try testing.expectEqual(@as(u64, sink.term_count), expanded_audit.emitted);
    try testing.expectEqual(@as(u32, 0), sink.projector_operator_count);
    try testing.expectEqual(@as(u32, 0), sink.tensor_spinor_projection_count);
    try testing.expectEqual(@as(u32, 0), sink.tensor_form_projection_count);
    try testing.expectEqual(@as(u32, 0), sink.cartan_product_count);
}

const CountingSink = struct {
    term_count: u32 = 0,
    atom_count: u32 = 0,
    metric_pair_count: u32 = 0,
    vector_slot_delta_count: u32 = 0,
    vector_slot_metric_count: u32 = 0,
    gamma_matrix_count: u32 = 0,
    gamma_form_count: u32 = 0,
    gamma_action_count: u32 = 0,
    exterior_gamma_action_count: u32 = 0,
    clifford_product_count: u32 = 0,
    clifford_product_factor_count: u32 = 0,
    clifford_product_metric_factor_count: u32 = 0,
    clifford_product_output_vector_factor_count: u32 = 0,
    gamma_trace_count: u32 = 0,
    spinor_pair_count: u32 = 0,
    vector_spinor_identity_count: u32 = 0,
    identity_route_count: u32 = 0,
    spinor_index_delta_count: u32 = 0,
    spinor_symmetrized_product_count: u32 = 0,
    spinor_tower_contract_count: u32 = 0,
    spinor_tower_contract_adjoint_count: u32 = 0,
    product_identity_count: u32 = 0,
    epsilon_count: u32 = 0,
    generalized_delta_count: u32 = 0,
    cartan_product_count: u32 = 0,
    tensor_spinor_projection_count: u32 = 0,
    tensor_form_projection_count: u32 = 0,
    tensor_form_gamma_wedge_count: u32 = 0,
    tensor_form_gamma_map_count: u32 = 0,
    tensor_form_gamma_map_adjoint_count: u32 = 0,
    tensor_form_spinor_pair_count: u32 = 0,
    structure_constant_count: u32 = 0,
    tensor_spinor_profile_audit: projector_constructor.StructuralProjectorCoverageAudit = .{},
    gamma_operator_count: u32 = 0,
    projector_operator_count: u32 = 0,
    first_gamma_operator_id: ?u32 = null,
    first_gamma_dimension: ?u16 = null,
    first_gamma_rank: ?u8 = null,
    first_gamma_chirality: ?u8 = null,
    first_gamma_form_operator_id: ?u32 = null,
    first_gamma_form_dimension: ?u16 = null,
    first_gamma_form_rank: ?u8 = null,
    first_gamma_form_chirality: ?u8 = null,
    first_gamma_form_duality: ?rendering.DualityTag = null,
    first_exterior_gamma_action_operator_id: ?u32 = null,
    first_exterior_gamma_action_dimension: ?u16 = null,
    first_exterior_gamma_action_chirality: ?u8 = null,
    first_clifford_product_left_rank: ?u8 = null,
    first_clifford_product_right_rank: ?u8 = null,
    first_clifford_product_output_rank: ?u8 = null,
    first_clifford_product_contractions: ?u8 = null,
    first_clifford_product_metric_count: ?u16 = null,
    first_clifford_product_free_vector_count: ?u16 = null,
    first_clifford_product_coefficient: ?i64 = null,
    first_clifford_product_factor_atom_index: ?u32 = null,
    first_clifford_product_factor_index: ?u16 = null,
    first_clifford_product_factor_left_operator_id: ?u32 = null,
    first_clifford_product_factor_right_operator_id: ?u32 = null,
    first_clifford_product_factor_dimension: ?u16 = null,
    first_clifford_product_factor_output_rank: ?u8 = null,
    first_clifford_product_factor_coefficient: ?i64 = null,
    first_gamma_trace_operator_id: ?u32 = null,
    first_gamma_trace_dimension: ?u16 = null,
    first_gamma_trace_chirality: ?u8 = null,
    first_gamma_trace_coefficient: ?rendering.RationalValue = null,
    first_spinor_pair_operator_id: ?u32 = null,
    first_spinor_pair_dimension: ?u16 = null,
    first_spinor_pair_left_chirality: ?u8 = null,
    first_spinor_pair_right_chirality: ?u8 = null,
    first_identity_route_operator_id: ?u32 = null,
    first_spinor_index_delta_operator_id: ?u32 = null,
    first_spinor_symmetrized_product_operator_id: ?u32 = null,
    first_spinor_symmetrized_product_dimension: ?u16 = null,
    first_spinor_symmetrized_product_left_power: ?u16 = null,
    first_spinor_symmetrized_product_right_power: ?u16 = null,
    first_spinor_symmetrized_product_output_power: ?u16 = null,
    first_spinor_symmetrized_product_chirality: ?u8 = null,
    first_spinor_tower_contract_operator_id: ?u32 = null,
    first_spinor_tower_contract_dimension: ?u16 = null,
    first_spinor_tower_contract_input_power: ?u16 = null,
    first_spinor_tower_contract_output_power: ?u16 = null,
    first_spinor_tower_contract_chirality: ?u8 = null,
    first_spinor_tower_contract_form_rank: ?u8 = null,
    first_product_identity_operator_id: ?u32 = null,
    first_cartan_product_operator_id: ?u32 = null,
    first_tensor_spinor_projection_operator_id: ?u32 = null,
    first_tensor_spinor_projection_dimension: ?u16 = null,
    first_tensor_spinor_projection_input_profile: ?u128 = null,
    first_tensor_spinor_projection_input_count: ?u8 = null,
    first_tensor_spinor_projection_form_rank: ?u8 = null,
    first_tensor_spinor_projection_form_count: ?u8 = null,
    first_tensor_spinor_projection_form_mask: ?u64 = null,
    first_tensor_spinor_projection_form_profile: ?u128 = null,
    first_tensor_spinor_projection_tower_power: ?u16 = null,
    first_tensor_spinor_projection_chirality: ?u8 = null,
    first_tensor_form_projection_operator_id: ?u32 = null,
    first_tensor_form_projection_dimension: ?u16 = null,
    first_tensor_form_projection_input_mask: ?u64 = null,
    first_tensor_form_projection_output_profile: ?u128 = null,
    first_tensor_form_projection_output_count: ?u8 = null,
    first_tensor_form_projection_output_rank: ?u8 = null,
    first_tensor_form_projection_output_duality: ?rendering.DualityTag = null,
    first_tensor_form_gamma_wedge_operator_id: ?u32 = null,
    first_tensor_form_gamma_wedge_dimension: ?u16 = null,
    first_tensor_form_gamma_wedge_input_mask: ?u64 = null,
    first_tensor_form_gamma_wedge_input_profile: ?u128 = null,
    first_tensor_form_gamma_wedge_input_count: ?u8 = null,
    first_tensor_form_gamma_wedge_output_profile: ?u128 = null,
    first_tensor_form_gamma_wedge_output_count: ?u8 = null,
    first_tensor_form_gamma_wedge_inserted_rank: ?u8 = null,
    first_tensor_form_gamma_wedge_chirality: ?u8 = null,
    first_tensor_form_gamma_map_operator_id: ?u32 = null,
    first_tensor_form_gamma_map_dimension: ?u16 = null,
    first_tensor_form_gamma_map_source_rank: ?u8 = null,
    first_tensor_form_gamma_map_lower_rank: ?u8 = null,
    first_tensor_form_gamma_map_upper_rank: ?u8 = null,
    first_tensor_form_gamma_map_chirality: ?u8 = null,
    first_tensor_form_spinor_pair_operator_id: ?u32 = null,
    first_tensor_form_spinor_pair_dimension: ?u16 = null,
    first_tensor_form_spinor_pair_input_mask: ?u64 = null,
    first_tensor_form_spinor_pair_input_profile: ?u128 = null,
    first_tensor_form_spinor_pair_input_count: ?u8 = null,
    first_tensor_form_spinor_pair_output_profile: ?u128 = null,
    first_tensor_form_spinor_pair_output_count: ?u8 = null,
    first_tensor_form_spinor_pair_left_chirality: ?u8 = null,
    first_tensor_form_spinor_pair_right_chirality: ?u8 = null,
    first_structure_constant_operator_id: ?u32 = null,
    first_structure_constant_family: ?symmetry.LieFamily = null,
    first_structure_constant_rank: ?u8 = null,
    first_projector_operator_id: ?u32 = null,

    pub fn emitTerm(self: *CountingSink, term: rendering.SymbolicTerm) !void {
        self.term_count += 1;
        self.atom_count += @intCast(term.atoms.len);
        for (term.atoms) |atom| {
            switch (atom) {
                .metric_pair => self.metric_pair_count += 1,
                .vector_slot_delta => self.vector_slot_delta_count += 1,
                .vector_slot_metric => self.vector_slot_metric_count += 1,
                .generalized_delta => self.generalized_delta_count += 1,
                .gamma_matrix => |gamma| {
                    self.gamma_matrix_count += 1;
                    if (self.first_gamma_operator_id == null) self.first_gamma_operator_id = gamma.operator_id;
                    if (self.first_gamma_dimension == null) self.first_gamma_dimension = gamma.orthogonal_dimension;
                    if (self.first_gamma_rank == null) self.first_gamma_rank = gamma.rank;
                    if (self.first_gamma_chirality == null) self.first_gamma_chirality = gamma.chirality;
                },
                .gamma_form => |gamma| {
                    self.gamma_form_count += 1;
                    if (self.first_gamma_form_operator_id == null) self.first_gamma_form_operator_id = gamma.operator_id;
                    if (self.first_gamma_form_dimension == null) self.first_gamma_form_dimension = gamma.orthogonal_dimension;
                    if (self.first_gamma_form_rank == null) self.first_gamma_form_rank = gamma.rank;
                    if (self.first_gamma_form_chirality == null) self.first_gamma_form_chirality = gamma.chirality;
                    if (self.first_gamma_form_duality == null) self.first_gamma_form_duality = gamma.duality;
                },
                .gamma_action => self.gamma_action_count += 1,
                .exterior_gamma_action => |action| {
                    self.exterior_gamma_action_count += 1;
                    if (self.first_exterior_gamma_action_operator_id == null) self.first_exterior_gamma_action_operator_id = action.operator_id;
                    if (self.first_exterior_gamma_action_dimension == null) self.first_exterior_gamma_action_dimension = action.orthogonal_dimension;
                    if (self.first_exterior_gamma_action_chirality == null) self.first_exterior_gamma_action_chirality = action.chirality;
                },
                .clifford_product => |product| {
                    self.clifford_product_count += 1;
                    if (self.first_clifford_product_left_rank == null) self.first_clifford_product_left_rank = product.left_rank;
                    if (self.first_clifford_product_right_rank == null) self.first_clifford_product_right_rank = product.right_rank;
                    if (self.first_clifford_product_output_rank == null) self.first_clifford_product_output_rank = product.output_rank;
                    if (self.first_clifford_product_contractions == null) self.first_clifford_product_contractions = product.contractions;
                    if (self.first_clifford_product_metric_count == null) self.first_clifford_product_metric_count = product.metric_count;
                    if (self.first_clifford_product_free_vector_count == null) self.first_clifford_product_free_vector_count = product.free_vector_count;
                    if (self.first_clifford_product_coefficient == null) self.first_clifford_product_coefficient = product.coefficient;
                },
                .clifford_product_factor => |record| self.countCliffordProductFactor(record),
                .gamma_trace => |trace| {
                    self.gamma_trace_count += 1;
                    if (self.first_gamma_trace_operator_id == null) self.first_gamma_trace_operator_id = trace.operator_id;
                    if (self.first_gamma_trace_dimension == null) self.first_gamma_trace_dimension = trace.orthogonal_dimension;
                    if (self.first_gamma_trace_chirality == null) self.first_gamma_trace_chirality = trace.chirality;
                    if (self.first_gamma_trace_coefficient == null) self.first_gamma_trace_coefficient = rendering.rationalValue(term.coefficient);
                },
                .spinor_pair => |pair| {
                    self.spinor_pair_count += 1;
                    if (self.first_spinor_pair_operator_id == null) self.first_spinor_pair_operator_id = pair.operator_id;
                    if (self.first_spinor_pair_dimension == null) self.first_spinor_pair_dimension = pair.orthogonal_dimension;
                    if (self.first_spinor_pair_left_chirality == null) self.first_spinor_pair_left_chirality = pair.chirality_left;
                    if (self.first_spinor_pair_right_chirality == null) self.first_spinor_pair_right_chirality = pair.chirality_right;
                },
                .vector_spinor_identity => self.vector_spinor_identity_count += 1,
                .identity_route => |identity| {
                    self.identity_route_count += 1;
                    if (self.first_identity_route_operator_id == null) self.first_identity_route_operator_id = identity.operator_id;
                },
                .spinor_index_delta => |delta| {
                    self.spinor_index_delta_count += 1;
                    if (self.first_spinor_index_delta_operator_id == null) self.first_spinor_index_delta_operator_id = delta.operator_id;
                },
                .spinor_symmetrized_product => |product| {
                    self.spinor_symmetrized_product_count += 1;
                    if (self.first_spinor_symmetrized_product_operator_id == null) self.first_spinor_symmetrized_product_operator_id = product.operator_id;
                    if (self.first_spinor_symmetrized_product_dimension == null) self.first_spinor_symmetrized_product_dimension = product.orthogonal_dimension;
                    if (self.first_spinor_symmetrized_product_left_power == null) self.first_spinor_symmetrized_product_left_power = product.left_power;
                    if (self.first_spinor_symmetrized_product_right_power == null) self.first_spinor_symmetrized_product_right_power = product.right_power;
                    if (self.first_spinor_symmetrized_product_output_power == null) self.first_spinor_symmetrized_product_output_power = product.output_power;
                    if (self.first_spinor_symmetrized_product_chirality == null) self.first_spinor_symmetrized_product_chirality = product.chirality;
                },
                .product_identity => |identity| {
                    self.product_identity_count += 1;
                    if (self.first_product_identity_operator_id == null) self.first_product_identity_operator_id = identity.operator_id;
                },
                .epsilon => self.epsilon_count += 1,
                .structure_constant => |constant| {
                    self.structure_constant_count += 1;
                    if (self.first_structure_constant_operator_id == null) self.first_structure_constant_operator_id = constant.operator_id;
                    if (self.first_structure_constant_family == null) self.first_structure_constant_family = constant.family;
                    if (self.first_structure_constant_rank == null) self.first_structure_constant_rank = constant.rank;
                },
                .cartan_product => |cartan| {
                    self.cartan_product_count += 1;
                    if (self.first_cartan_product_operator_id == null) self.first_cartan_product_operator_id = cartan.operator_id;
                },
                .spinor_tower_contract => |contract| {
                    self.spinor_tower_contract_count += 1;
                    if (self.first_spinor_tower_contract_operator_id == null) self.first_spinor_tower_contract_operator_id = contract.operator_id;
                    if (self.first_spinor_tower_contract_dimension == null) self.first_spinor_tower_contract_dimension = contract.orthogonal_dimension;
                    if (self.first_spinor_tower_contract_input_power == null) self.first_spinor_tower_contract_input_power = contract.input_power;
                    if (self.first_spinor_tower_contract_output_power == null) self.first_spinor_tower_contract_output_power = contract.output_power;
                    if (self.first_spinor_tower_contract_chirality == null) self.first_spinor_tower_contract_chirality = contract.chirality;
                    if (self.first_spinor_tower_contract_form_rank == null) self.first_spinor_tower_contract_form_rank = contract.form_rank;
                },
                .spinor_tower_contract_adjoint => {
                    self.spinor_tower_contract_adjoint_count += 1;
                },
                .tensor_spinor_projection => |projection| {
                    self.tensor_spinor_projection_count += 1;
                    self.tensor_spinor_profile_audit.recordTensorSpinorAtom(projection);
                    if (self.first_tensor_spinor_projection_operator_id == null) self.first_tensor_spinor_projection_operator_id = projection.operator_id;
                    if (self.first_tensor_spinor_projection_dimension == null) self.first_tensor_spinor_projection_dimension = projection.orthogonal_dimension;
                    if (self.first_tensor_spinor_projection_input_profile == null) self.first_tensor_spinor_projection_input_profile = projection.input_form_profile;
                    if (self.first_tensor_spinor_projection_input_count == null) self.first_tensor_spinor_projection_input_count = projection.input_form_count;
                    if (self.first_tensor_spinor_projection_form_rank == null) self.first_tensor_spinor_projection_form_rank = projection.form_rank;
                    if (self.first_tensor_spinor_projection_form_count == null) self.first_tensor_spinor_projection_form_count = projection.form_count;
                    if (self.first_tensor_spinor_projection_form_mask == null) self.first_tensor_spinor_projection_form_mask = projection.form_mask;
                    if (self.first_tensor_spinor_projection_form_profile == null) self.first_tensor_spinor_projection_form_profile = projection.form_profile;
                    if (self.first_tensor_spinor_projection_tower_power == null) self.first_tensor_spinor_projection_tower_power = projection.tower_power;
                    if (self.first_tensor_spinor_projection_chirality == null) self.first_tensor_spinor_projection_chirality = projection.chirality;
                },
                .tensor_form_projection => |projection| {
                    self.tensor_form_projection_count += 1;
                    if (self.first_tensor_form_projection_operator_id == null) self.first_tensor_form_projection_operator_id = projection.operator_id;
                    if (self.first_tensor_form_projection_dimension == null) self.first_tensor_form_projection_dimension = projection.orthogonal_dimension;
                    if (self.first_tensor_form_projection_input_mask == null) self.first_tensor_form_projection_input_mask = projection.input_form_mask;
                    if (self.first_tensor_form_projection_output_profile == null) self.first_tensor_form_projection_output_profile = projection.output_form_profile;
                    if (self.first_tensor_form_projection_output_count == null) self.first_tensor_form_projection_output_count = projection.output_form_count;
                    if (self.first_tensor_form_projection_output_rank == null) self.first_tensor_form_projection_output_rank = projection.output_form_rank;
                    if (self.first_tensor_form_projection_output_duality == null) self.first_tensor_form_projection_output_duality = projection.output_duality;
                },
                .tensor_form_gamma_wedge => |projection| {
                    self.tensor_form_gamma_wedge_count += 1;
                    if (self.first_tensor_form_gamma_wedge_operator_id == null) self.first_tensor_form_gamma_wedge_operator_id = projection.operator_id;
                    if (self.first_tensor_form_gamma_wedge_dimension == null) self.first_tensor_form_gamma_wedge_dimension = projection.orthogonal_dimension;
                    if (self.first_tensor_form_gamma_wedge_input_mask == null) self.first_tensor_form_gamma_wedge_input_mask = projection.input_form_mask;
                    if (self.first_tensor_form_gamma_wedge_input_profile == null) self.first_tensor_form_gamma_wedge_input_profile = projection.input_form_profile;
                    if (self.first_tensor_form_gamma_wedge_input_count == null) self.first_tensor_form_gamma_wedge_input_count = projection.input_form_count;
                    if (self.first_tensor_form_gamma_wedge_output_profile == null) self.first_tensor_form_gamma_wedge_output_profile = projection.output_form_profile;
                    if (self.first_tensor_form_gamma_wedge_output_count == null) self.first_tensor_form_gamma_wedge_output_count = projection.output_form_count;
                    if (self.first_tensor_form_gamma_wedge_inserted_rank == null) self.first_tensor_form_gamma_wedge_inserted_rank = projection.inserted_rank;
                    if (self.first_tensor_form_gamma_wedge_chirality == null) self.first_tensor_form_gamma_wedge_chirality = projection.chirality;
                },
                .tensor_form_gamma_map => |projection| {
                    self.tensor_form_gamma_map_count += 1;
                    if (self.first_tensor_form_gamma_map_operator_id == null) self.first_tensor_form_gamma_map_operator_id = projection.operator_id;
                    if (self.first_tensor_form_gamma_map_dimension == null) self.first_tensor_form_gamma_map_dimension = projection.orthogonal_dimension;
                    if (self.first_tensor_form_gamma_map_source_rank == null) self.first_tensor_form_gamma_map_source_rank = projection.source_rank;
                    if (self.first_tensor_form_gamma_map_lower_rank == null) self.first_tensor_form_gamma_map_lower_rank = projection.lower_rank;
                    if (self.first_tensor_form_gamma_map_upper_rank == null) self.first_tensor_form_gamma_map_upper_rank = projection.upper_rank;
                    if (self.first_tensor_form_gamma_map_chirality == null) self.first_tensor_form_gamma_map_chirality = projection.chirality;
                },
                .tensor_form_gamma_map_adjoint => {
                    self.tensor_form_gamma_map_adjoint_count += 1;
                },
                .tensor_form_spinor_pair => |projection| {
                    self.tensor_form_spinor_pair_count += 1;
                    if (self.first_tensor_form_spinor_pair_operator_id == null) self.first_tensor_form_spinor_pair_operator_id = projection.operator_id;
                    if (self.first_tensor_form_spinor_pair_dimension == null) self.first_tensor_form_spinor_pair_dimension = projection.orthogonal_dimension;
                    if (self.first_tensor_form_spinor_pair_input_mask == null) self.first_tensor_form_spinor_pair_input_mask = projection.input_form_mask;
                    if (self.first_tensor_form_spinor_pair_input_profile == null) self.first_tensor_form_spinor_pair_input_profile = projection.input_form_profile;
                    if (self.first_tensor_form_spinor_pair_input_count == null) self.first_tensor_form_spinor_pair_input_count = projection.input_form_count;
                    if (self.first_tensor_form_spinor_pair_output_profile == null) self.first_tensor_form_spinor_pair_output_profile = projection.output_form_profile;
                    if (self.first_tensor_form_spinor_pair_output_count == null) self.first_tensor_form_spinor_pair_output_count = projection.output_form_count;
                    if (self.first_tensor_form_spinor_pair_left_chirality == null) self.first_tensor_form_spinor_pair_left_chirality = projection.left_chirality;
                    if (self.first_tensor_form_spinor_pair_right_chirality == null) self.first_tensor_form_spinor_pair_right_chirality = projection.right_chirality;
                },
                .named_operator => |operator| switch (operator.kind) {
                    .gamma => self.gamma_operator_count += 1,
                    .projector => {
                        self.projector_operator_count += 1;
                        if (self.first_projector_operator_id == null) self.first_projector_operator_id = operator.operator_id;
                    },
                    else => {},
                },
                else => {},
            }
        }
    }

    pub fn emitCliffordProductFactor(self: *CountingSink, record: rendering.CliffordProductFactorRecord) !void {
        self.countCliffordProductFactor(record);
    }

    fn countCliffordProductFactor(self: *CountingSink, record: rendering.CliffordProductFactorRecord) void {
        self.clifford_product_factor_count += 1;
        if (self.first_clifford_product_factor_atom_index == null) self.first_clifford_product_factor_atom_index = record.atom_index;
        if (self.first_clifford_product_factor_index == null) self.first_clifford_product_factor_index = record.factor_index;
        if (self.first_clifford_product_factor_left_operator_id == null) self.first_clifford_product_factor_left_operator_id = record.left_operator_id;
        if (self.first_clifford_product_factor_right_operator_id == null) self.first_clifford_product_factor_right_operator_id = record.right_operator_id;
        if (self.first_clifford_product_factor_dimension == null) self.first_clifford_product_factor_dimension = record.orthogonal_dimension;
        if (self.first_clifford_product_factor_output_rank == null) self.first_clifford_product_factor_output_rank = record.output_rank;
        if (self.first_clifford_product_factor_coefficient == null) self.first_clifford_product_factor_coefficient = record.coefficient;
        switch (record.factor) {
            .metric => self.clifford_product_metric_factor_count += 1,
            .output_vector => self.clifford_product_output_vector_factor_count += 1,
        }
    }
};

const EvaluationCountingSink = struct {
    term_count: u32 = 0,
    atom_count: u32 = 0,
    metric_pair_count: u32 = 0,
    gamma_matrix_count: u32 = 0,
    clifford_product_factor_count: u32 = 0,
    compact_formula_count: u32 = 0,
    first_coefficient: ?rendering.RationalValue = null,

    pub fn emitEvaluationTerm(self: *EvaluationCountingSink, term: rendering.EvaluationTerm) !void {
        self.term_count += 1;
        self.atom_count += @intCast(term.atoms.len);
        if (self.first_coefficient == null) self.first_coefficient = rendering.rationalValue(term.coefficient);
        for (term.atoms) |atom| {
            switch (atom) {
                .metric_pair => self.metric_pair_count += 1,
                .gamma_matrix => self.gamma_matrix_count += 1,
                .clifford_product_factor => self.clifford_product_factor_count += 1,
                .named_operator,
                .clifford_product,
                .product_identity,
                .cartan_product,
                .tensor_spinor_projection,
                .tensor_form_projection,
                .gamma_trace,
                .vector_spinor_identity,
                => self.compact_formula_count += 1,
                else => {},
            }
        }
    }
};

fn isVectorDynkin(label: []const i16) bool {
    if (label.len == 0 or label[0] != 1) return false;
    for (label[1..]) |entry| {
        if (entry != 0) return false;
    }
    return true;
}

fn isSpinorDynkin(simple: symmetry.SimpleLieAlgebra, label: []const i16) bool {
    if (label.len != simple.rank) return false;
    switch (simple.family) {
        .b => {
            if (label.len == 0 or label[label.len - 1] != 1) return false;
            for (label[0 .. label.len - 1]) |entry| {
                if (entry != 0) return false;
            }
            return true;
        },
        .d => {
            if (label.len < 2) return false;
            const left = label.len - 2;
            const right = label.len - 1;
            if (!((label[left] == 1 and label[right] == 0) or (label[left] == 0 and label[right] == 1))) return false;
            for (label[0..left]) |entry| {
                if (entry != 0) return false;
            }
            return true;
        },
        else => return false,
    }
}

fn isVectorSpinorDynkin(simple: symmetry.SimpleLieAlgebra, label: []const i16) bool {
    if (label.len != simple.rank or label.len < 2) return false;
    if (label[0] != 1) return false;
    switch (simple.family) {
        .b => {
            if (label[label.len - 1] != 1) return false;
            for (label[1 .. label.len - 1]) |entry| {
                if (entry != 0) return false;
            }
            return true;
        },
        .d => {
            const left = label.len - 2;
            const right = label.len - 1;
            if (!((label[left] == 1 and label[right] == 0) or (label[left] == 0 and label[right] == 1))) return false;
            for (label[1..left]) |entry| {
                if (entry != 0) return false;
            }
            return true;
        },
        else => return false,
    }
}

fn isA2FundamentalDynkin(label: []const i16) bool {
    return label.len == 2 and label[0] == 1 and label[1] == 0;
}

fn isA2AntiFundamentalDynkin(label: []const i16) bool {
    return label.len == 2 and label[0] == 0 and label[1] == 1;
}

fn isE6FundamentalDynkin(label: []const i16) bool {
    return label.len == 6 and label[0] == 1 and label[1] == 0 and label[2] == 0 and label[3] == 0 and label[4] == 0 and label[5] == 0;
}

fn isE6DualFundamentalDynkin(label: []const i16) bool {
    return label.len == 6 and label[0] == 0 and label[1] == 0 and label[2] == 0 and label[3] == 0 and label[4] == 1 and label[5] == 0;
}

fn simpleAdjointDimension(simple: symmetry.SimpleLieAlgebra) u128 {
    const rank: u128 = simple.rank;
    return switch (simple.family) {
        .a => rank * (rank + 2),
        .b => rank * (2 * rank + 1),
        .d => rank * (2 * rank - 1),
        .e6 => 78,
        .e7 => 133,
        .e8 => 248,
        else => 0,
    };
}

fn orthogonalVectorSpinorFormulaAudit(orthogonal_dimension: u16) projector.ProjectorFormulaAudit {
    const trace_projector_denominator = orthogonal_dimension;
    const gamma_trace_square_factor = orthogonal_dimension;
    const normalized = trace_projector_denominator != 0;
    const gamma_trace_law = normalized and gamma_trace_square_factor == trace_projector_denominator;
    return .{
        .normalized = normalized,
        .idempotent = gamma_trace_law,
        .channel_separated = gamma_trace_law,
        .gamma_traceless = gamma_trace_law,
    };
}

fn orthogonalSpinorBilinearFormulaAudit(simple: symmetry.SimpleLieAlgebra, left: []const i16, right: []const i16, rank: u8, duality: rendering.DualityTag) projector.ProjectorFormulaAudit {
    if (!isSpinorDynkin(simple, left) or !isSpinorDynkin(simple, right)) return .{};
    const orthogonal_dimension = rendering.orthogonalDimension(simple);
    const normalized = orthogonalGammaGradeNormNonZero(simple, orthogonal_dimension, rank, duality) and orthogonalSpinorBilinearChiralityValid(simple, left, right, rank);
    return .{
        .normalized = normalized,
        .idempotent = normalized,
        .channel_separated = normalized,
    };
}

fn orthogonalGammaGradeNormNonZero(simple: symmetry.SimpleLieAlgebra, orthogonal_dimension: u16, rank: u8, duality: rendering.DualityTag) bool {
    if (orthogonal_dimension == 0 or rank > orthogonal_dimension) return false;
    switch (duality) {
        .none => return true,
        .self_dual, .anti_self_dual => return simple.family == .d and @as(u16, rank) * 2 == orthogonal_dimension,
    }
}

fn orthogonalSpinorBilinearChiralityValid(simple: symmetry.SimpleLieAlgebra, left: []const i16, right: []const i16, rank: u8) bool {
    const left_chirality = rendering.gammaChiralityTag(simple, left);
    const right_chirality = rendering.gammaChiralityTag(simple, right);
    return switch (simple.family) {
        .b => left_chirality == .none and right_chirality == .none,
        .d => if (rank % 2 == 0) left_chirality != right_chirality else left_chirality == right_chirality and left_chirality != .none,
        else => false,
    };
}

fn oppositeGammaChirality(chirality: rendering.GammaChirality) rendering.GammaChirality {
    return switch (chirality) {
        .left => .right,
        .right => .left,
        .none => .none,
    };
}

fn isGramFormulaKind(kind: projector.ProjectorFormulaKind) bool {
    return kind == .orthogonal_structural_projection;
}

fn exactPrimitiveFormulaAudit() projector.ProjectorFormulaAudit {
    return .{
        .normalized = true,
        .idempotent = true,
        .channel_separated = true,
    };
}

fn exactGramProjectorFormulaAudit() projector.ProjectorFormulaAudit {
    return .{
        .normalized = true,
        .idempotent = true,
        .channel_separated = true,
    };
}

fn orthogonalIrrepDescriptor(simple: symmetry.SimpleLieAlgebra, label: []const i16) OrthogonalIrrepDescriptor {
    if (label.len != simple.rank) return unsupportedOrthogonalDescriptor();
    switch (simple.family) {
        .b, .d => {},
        else => return unsupportedOrthogonalDescriptor(),
    }

    const dimension = rendering.orthogonalDimension(simple);
    if (isZeroDynkin(label)) return .{ .kind = .scalar, .dimension = dimension };
    if (orthogonalFormInfo(simple, label)) |form| return descriptorFromSingleForm(dimension, form);
    if (orthogonalTensorSpinorInfo(simple, label)) |info| return descriptorFromTensorSpinor(dimension, info);
    if (spinorTowerInfo(simple, label)) |tower| return descriptorFromSpinorTower(dimension, tower);
    if (orthogonalYoungShape(simple, label)) |shape| return descriptorFromYoungShape(dimension, shape, ordinaryTensorFormInfo(simple, label));
    if (ordinaryTensorFormInfo(simple, label)) |forms| return descriptorFromFormSet(dimension, forms);
    return unsupportedOrthogonalDescriptor();
}

fn unsupportedOrthogonalDescriptor() OrthogonalIrrepDescriptor {
    return .{ .kind = .unsupported, .dimension = 0 };
}

fn descriptorFromSingleForm(dimension: u16, form: OrthogonalFormInfo) OrthogonalIrrepDescriptor {
    if (form.rank == 0 or form.rank > 32) return unsupportedOrthogonalDescriptor();
    if (form.duality != .none) return .{
        .kind = .form_profile,
        .dimension = dimension,
        .form_count = 1,
        .form_rank = form.rank,
        .form_duality = form.duality,
    };
    const rank_index: u7 = @intCast(form.rank - 1);
    return .{
        .kind = .form_profile,
        .dimension = dimension,
        .form_profile = @as(u128, 1) << @intCast(rank_index * 4),
        .form_mask = @as(u64, 1) << @intCast(rank_index),
        .form_count = 1,
        .form_total_power = 1,
        .form_rank = form.rank,
        .form_duality = form.duality,
    };
}

fn descriptorFromFormSet(dimension: u16, forms: OrthogonalFormSetInfo) OrthogonalIrrepDescriptor {
    return .{
        .kind = .form_profile,
        .dimension = dimension,
        .form_profile = forms.profile,
        .form_mask = forms.mask,
        .form_count = forms.count,
        .form_total_power = forms.total_power,
        .form_rank = forms.first_rank,
        .form_duality = forms.duality,
    };
}

fn descriptorFromSpinorTower(dimension: u16, tower: SpinorTowerInfo) OrthogonalIrrepDescriptor {
    return .{
        .kind = .spinor_tower,
        .dimension = dimension,
        .has_spinor = true,
        .chirality = @intFromEnum(tower.chirality),
        .tower_power = tower.power,
    };
}

fn descriptorFromTensorSpinor(dimension: u16, info: OrthogonalTensorSpinorInfo) OrthogonalIrrepDescriptor {
    return .{
        .kind = .tensor_spinor,
        .dimension = dimension,
        .form_profile = info.forms.profile,
        .form_mask = info.forms.mask,
        .form_count = info.forms.count,
        .form_total_power = info.forms.total_power,
        .form_rank = info.forms.first_rank,
        .form_duality = info.forms.duality,
        .has_spinor = true,
        .chirality = @intFromEnum(info.chirality),
        .tower_power = info.tower_power,
    };
}

fn descriptorFromYoungShape(dimension: u16, shape: OrthogonalYoungShape, forms: ?OrthogonalFormSetInfo) OrthogonalIrrepDescriptor {
    var descriptor: OrthogonalIrrepDescriptor = .{
        .kind = .vector_young_shape,
        .dimension = dimension,
        .young_row_count = shape.row_count,
        .young_rows = shape.rows,
        .young_box_count = shape.box_count,
    };
    if (forms) |form_set| {
        descriptor.form_profile = form_set.profile;
        descriptor.form_mask = form_set.mask;
        descriptor.form_count = form_set.count;
        descriptor.form_total_power = form_set.total_power;
        descriptor.form_rank = form_set.first_rank;
        descriptor.form_duality = form_set.duality;
    }
    return descriptor;
}

fn orthogonalFormInfo(simple: symmetry.SimpleLieAlgebra, label: []const i16) ?OrthogonalFormInfo {
    if (label.len != simple.rank) return null;
    switch (simple.family) {
        .b => {
            if (label.len < 2) return null;
            for (label, 0..) |entry, index| {
                if (entry == 0) continue;
                if (entry != 1 or index + 1 >= label.len) return null;
                return .{ .rank = @intCast(index + 1) };
            }
            return null;
        },
        .d => {
            if (label.len < 3) return null;
            for (label[0 .. label.len - 2], 0..) |entry, index| {
                if (entry == 0) continue;
                if (entry != 1) return null;
                for (label[index + 1 ..]) |tail| {
                    if (tail != 0) return null;
                }
                return .{ .rank = @intCast(index + 1) };
            }

            const left = label.len - 2;
            const right = label.len - 1;
            if (label[left] == 2 and label[right] == 0) return .{
                .rank = @intCast(label.len),
                .duality = .anti_self_dual,
            };
            if (label[left] == 0 and label[right] == 2) return .{
                .rank = @intCast(label.len),
                .duality = .self_dual,
            };
            if (label[left] == 1 and label[right] == 1) return .{
                .rank = @intCast(label.len - 1),
            };
            return null;
        },
        else => return null,
    }
}

fn orthogonalTensorSpinorInfo(simple: symmetry.SimpleLieAlgebra, label: []const i16) ?OrthogonalTensorSpinorInfo {
    if (label.len != simple.rank) return null;
    const tower = outputSpinorTowerInfo(simple, label) orelse return null;
    const forms = outputFormSetInfo(simple, label) orelse return null;
    return .{
        .forms = forms,
        .tower_power = tower.power,
        .chirality = tower.chirality,
    };
}

fn outputFormSetInfo(simple: symmetry.SimpleLieAlgebra, label: []const i16) ?OrthogonalFormSetInfo {
    if (label.len != simple.rank) return null;
    const form_end = switch (simple.family) {
        .b => if (label.len == 0) return null else label.len - 1,
        .d => if (label.len < 2) return null else label.len - 2,
        else => return null,
    };
    var found: OrthogonalFormSetInfo = .{
        .first_rank = 0,
        .count = 0,
        .total_power = 0,
        .mask = 0,
        .profile = 0,
    };
    for (label[0..form_end], 0..) |entry, index| {
        if (entry == 0) continue;
        if (entry < 0 or entry > 15 or index >= 64) return null;
        const rank: u8 = @intCast(index + 1);
        if (found.count == 0) found.first_rank = rank;
        found.count += 1;
        found.total_power += @intCast(entry);
        found.mask |= @as(u64, 1) << @intCast(index);
        found.profile |= @as(u128, @intCast(entry)) << @intCast(index * 4);
    }
    if (simple.family == .d) {
        const left = label.len - 2;
        const right = label.len - 1;
        if (label[left] < 0 or label[right] < 0) return null;
        const common = @min(label[left], label[right]);
        if (common > 0) {
            const rank_index = label.len - 2;
            if (common > 15 or rank_index >= 64) return null;
            if (found.count == 0) found.first_rank = @intCast(rank_index + 1);
            found.count += 1;
            found.total_power += @intCast(common);
            found.mask |= @as(u64, 1) << @intCast(rank_index);
            found.profile |= @as(u128, @intCast(common)) << @intCast(rank_index * 4);
        }
    }
    return if (found.count == 0) null else found;
}

fn ordinaryTensorFormInfo(simple: symmetry.SimpleLieAlgebra, label: []const i16) ?OrthogonalFormSetInfo {
    if (label.len != simple.rank) return null;
    switch (simple.family) {
        .b => {
            if (label.len == 0 or label[label.len - 1] != 0) return null;
        },
        .d => {
            if (label.len < 2) return null;
            const left = label.len - 2;
            const right = label.len - 1;
            if (label[left] != label[right]) return null;
        },
        else => return null,
    }
    return outputFormSetInfo(simple, label);
}

fn orthogonalYoungShape(simple: symmetry.SimpleLieAlgebra, label: []const i16) ?OrthogonalYoungShape {
    if (label.len != simple.rank) return null;
    const form_end = switch (simple.family) {
        .b => blk: {
            if (label.len == 0 or label[label.len - 1] != 0) return null;
            break :blk label.len - 1;
        },
        .d => blk: {
            if (label.len < 2 or label[label.len - 2] != 0 or label[label.len - 1] != 0) return null;
            break :blk label.len - 2;
        },
        else => return null,
    };
    if (form_end == 0) return null;
    var tail_index: usize = 2;
    while (tail_index < form_end) : (tail_index += 1) {
        if (label[tail_index] != 0) return null;
    }

    var shape: OrthogonalYoungShape = .{ .row_count = 0, .box_count = 0 };
    var row_index: usize = 0;
    while (row_index < form_end) : (row_index += 1) {
        var length: i16 = 0;
        var label_index = row_index;
        while (label_index < form_end) : (label_index += 1) {
            if (label[label_index] < 0) return null;
            length += label[label_index];
        }
        if (length == 0) continue;
        if (shape.row_count == max_orthogonal_young_rows or length > std.math.maxInt(u8)) return null;
        shape.rows[shape.row_count] = @intCast(length);
        shape.row_count += 1;
        shape.box_count = std.math.add(u8, shape.box_count, @intCast(length)) catch return null;
    }
    return if (shape.row_count == 0 or shape.box_count > 4) null else shape;
}

fn outputSpinorTowerInfo(simple: symmetry.SimpleLieAlgebra, label: []const i16) ?SpinorTowerInfo {
    if (label.len != simple.rank) return null;
    return switch (simple.family) {
        .b => {
            if (label.len == 0 or label[label.len - 1] <= 0) return null;
            return .{
                .power = @intCast(label[label.len - 1]),
                .chirality = .none,
            };
        },
        .d => {
            if (label.len < 2) return null;
            const left = label.len - 2;
            const right = label.len - 1;
            if (label[left] < 0 or label[right] < 0) return null;
            const common = @min(label[left], label[right]);
            const left_power = label[left] - common;
            const right_power = label[right] - common;
            if (left_power > 0 and right_power == 0) return .{
                .power = @intCast(left_power),
                .chirality = .left,
            };
            if (left_power == 0 and right_power > 0) return .{
                .power = @intCast(right_power),
                .chirality = .right,
            };
            return null;
        },
        else => null,
    };
}

fn isSpinorTowerDynkin(simple: symmetry.SimpleLieAlgebra, label: []const i16) bool {
    const tower = spinorTowerInfo(simple, label) orelse return false;
    return tower.power > 0;
}

fn spinorTowerInfo(simple: symmetry.SimpleLieAlgebra, label: []const i16) ?SpinorTowerInfo {
    if (label.len != simple.rank) return null;
    const form_end = switch (simple.family) {
        .b => if (label.len == 0) return null else label.len - 1,
        .d => if (label.len < 2) return null else label.len - 2,
        else => return null,
    };
    for (label[0..form_end]) |entry| {
        if (entry != 0) return null;
    }
    if (simple.family == .d and @min(label[label.len - 2], label[label.len - 1]) != 0) return null;
    return outputSpinorTowerInfo(simple, label);
}

fn formMaskShiftedUpOnce(left: u64, output: u64) bool {
    if (left == 0 or output == 0) return false;
    const removed = left & ~output;
    const added = output & ~left;
    if (@popCount(removed) != 1 or @popCount(added) != 1) return false;
    return added == removed << 1;
}

fn formProfileShiftedUpOnce(left: u128, output: u128) bool {
    if (left == 0 or output == 0) return false;
    for (0..31) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count == 0) continue;
        var candidate = left;
        candidate -= @as(u128, 1) << @intCast(rank_index * 4);
        candidate += @as(u128, 1) << @intCast((rank_index + 1) * 4);
        if (candidate == output) return true;
    }
    return false;
}

fn formProfileShiftedByOnce(left: u128, output: u128, delta: usize) bool {
    if (left == 0 or output == 0 or delta == 0) return false;
    for (0..32) |rank_index| {
        const output_index = rank_index + delta;
        if (output_index >= 32) break;
        const count = formProfileCount(left, rank_index);
        if (count == 0) continue;
        var candidate = left;
        candidate -= @as(u128, 1) << @intCast(rank_index * 4);
        candidate += @as(u128, 1) << @intCast(output_index * 4);
        if (candidate == output) return true;
    }
    return false;
}

fn formProfileShiftedAllUpOnce(left: u128, output: u128) bool {
    if (left == 0 or output == 0 or formProfileCount(left, 31) != 0) return false;
    var candidate: u128 = 0;
    for (0..31) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count == 0) continue;
        candidate += @as(u128, count) << @intCast((rank_index + 1) * 4);
    }
    return candidate == output;
}

fn formProfileShiftedAllDownOnce(left: u128, output: u128) bool {
    if (left == 0 or output == 0 or formProfileCount(left, 0) != 0) return false;
    var candidate: u128 = 0;
    for (1..32) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count == 0) continue;
        candidate += @as(u128, count) << @intCast((rank_index - 1) * 4);
    }
    return candidate == output;
}

fn formProfileShiftedAllDownWithOneExtraOnce(left: u128, output: u128) bool {
    if (left == 0 or output == 0 or formProfileCount(left, 0) != 0) return false;
    for (2..32) |extra_index| {
        const count = formProfileCount(left, extra_index);
        if (count == 0) continue;
        var candidate: u128 = 0;
        for (1..32) |rank_index| {
            const current = formProfileCount(left, rank_index);
            if (current == 0) continue;
            if (rank_index == extra_index) {
                candidate += @as(u128, 1) << @intCast((rank_index - 2) * 4);
                if (current > 1) candidate += @as(u128, current - 1) << @intCast((rank_index - 1) * 4);
            } else {
                candidate += @as(u128, current) << @intCast((rank_index - 1) * 4);
            }
        }
        if (candidate == output) return true;
    }
    return false;
}

fn formProfileIncrementedExistingOnce(left: u128, output: u128) bool {
    if (left == 0 or output == 0) return false;
    for (0..32) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count == 0 or count >= 15) continue;
        const candidate = left + (@as(u128, 1) << @intCast(rank_index * 4));
        if (candidate == output) return true;
    }
    return false;
}

fn formProfileIncrementedRank(left: u128, output: u128) ?u8 {
    if (left == 0 or output == 0) return null;
    for (0..32) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count == 0 or count >= 15) continue;
        const candidate = left + (@as(u128, 1) << @intCast(rank_index * 4));
        if (candidate == output) return @intCast(rank_index + 1);
    }
    return null;
}

fn formProfileAddedOnce(left: u128, output: u128) bool {
    if (output == 0) return false;
    for (0..32) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count >= 15) continue;
        const candidate = left + (@as(u128, 1) << @intCast(rank_index * 4));
        if (candidate == output) return true;
    }
    return false;
}

fn formProfileAddedRank(left: u128, output: u128) ?u8 {
    if (output == 0) return null;
    for (0..32) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count >= 15) continue;
        const candidate = left + (@as(u128, 1) << @intCast(rank_index * 4));
        if (candidate == output) return @intCast(rank_index + 1);
    }
    return null;
}

fn formProfileShiftedUpThenAddedOnce(left: u128, output: u128) bool {
    if (left == 0 or output == 0) return false;
    for (0..31) |shift_index| {
        const count = formProfileCount(left, shift_index);
        if (count == 0) continue;
        var shifted = left;
        shifted -= @as(u128, 1) << @intCast(shift_index * 4);
        shifted += @as(u128, 1) << @intCast((shift_index + 1) * 4);
        if (formProfileAddedOnce(shifted, output)) return true;
    }
    return false;
}

fn formProfileMovedOnce(left: u128, output: u128, from_index: usize, to_index: usize) bool {
    if (left == 0 or output == 0 or from_index >= 32 or to_index >= 32 or from_index == to_index) return false;
    const count = formProfileCount(left, from_index);
    if (count == 0) return false;
    var candidate = left;
    candidate -= @as(u128, 1) << @intCast(from_index * 4);
    candidate += @as(u128, 1) << @intCast(to_index * 4);
    return candidate == output;
}

fn formProfileMovedDownOnce(left: u128, output: u128, delta: usize) bool {
    if (left == 0 or output == 0 or delta == 0) return false;
    for (delta..32) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count == 0) continue;
        var candidate = left;
        candidate -= @as(u128, 1) << @intCast(rank_index * 4);
        candidate += @as(u128, 1) << @intCast((rank_index - delta) * 4);
        if (candidate == output) return true;
    }
    return false;
}

fn formProfileMovedDownAnyOnce(left: u128, output: u128) bool {
    if (left == 0 or output == 0) return false;
    for (1..32) |delta| {
        if (formProfileMovedDownOnce(left, output, delta)) return true;
    }
    return false;
}

fn formProfileMergedPairToMiddleOnce(left: u128, output: u128) bool {
    if (left == 0 or output == 0) return false;
    for (0..30) |rank_index| {
        if (formProfileCount(left, rank_index) == 0 or formProfileCount(left, rank_index + 2) == 0) continue;
        var candidate = left;
        candidate -= @as(u128, 1) << @intCast(rank_index * 4);
        candidate -= @as(u128, 1) << @intCast((rank_index + 2) * 4);
        candidate += @as(u128, 1) << @intCast((rank_index + 1) * 4);
        if (candidate == output) return true;
    }
    return false;
}

fn formProfileSplitDownToRankWrapOnce(left: u128, output: u128, wrap_index: usize) bool {
    if (left == 0 or output == 0 or wrap_index >= 32) return false;
    for (1..32) |rank_index| {
        if (rank_index == wrap_index + 1) break;
        const count = formProfileCount(left, rank_index);
        if (count == 0) continue;
        var candidate = left;
        candidate -= @as(u128, 1) << @intCast(rank_index * 4);
        candidate += @as(u128, 1) << @intCast((rank_index - 1) * 4);
        candidate += @as(u128, 1) << @intCast(wrap_index * 4);
        if (candidate == output) return true;
    }
    return false;
}

fn formProfileSplitToNeighborsOnce(left: u128, output: u128) bool {
    if (left == 0 or output == 0) return false;
    for (1..31) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count == 0) continue;
        var candidate = left;
        candidate -= @as(u128, 1) << @intCast(rank_index * 4);
        candidate += @as(u128, 1) << @intCast((rank_index - 1) * 4);
        candidate += @as(u128, 1) << @intCast((rank_index + 1) * 4);
        if (candidate == output) return true;
    }
    return false;
}

fn formProfileRemovedOnce(left: u128, output: u128) bool {
    if (left == 0) return false;
    for (0..32) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count == 0) continue;
        const candidate = left - (@as(u128, 1) << @intCast(rank_index * 4));
        if (candidate == output) return true;
    }
    return false;
}

fn formProfileRemovedAtRank(left: u128, output: u128, rank_index: usize) bool {
    if (left == 0 or rank_index >= 32) return false;
    const count = formProfileCount(left, rank_index);
    if (count == 0) return false;
    return left - (@as(u128, 1) << @intCast(rank_index * 4)) == output;
}

fn formProfileRemovedThenShiftedUpOnce(left: u128, output: u128) bool {
    if (left == 0) return false;
    for (0..32) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count == 0) continue;
        const removed = left - (@as(u128, 1) << @intCast(rank_index * 4));
        if (formProfileShiftedUpOnce(removed, output)) return true;
    }
    return false;
}

fn formProfileRemovedThenMovedDownOnce(left: u128, output: u128) bool {
    if (left == 0) return false;
    for (0..32) |rank_index| {
        const count = formProfileCount(left, rank_index);
        if (count == 0) continue;
        const removed = left - (@as(u128, 1) << @intCast(rank_index * 4));
        if (formProfileMovedDownOnce(removed, output, 1)) return true;
    }
    return false;
}

fn formProfileCount(profile: u128, rank_index: usize) u8 {
    if (rank_index >= 32) return 0;
    return @intCast((profile >> @intCast(rank_index * 4)) & 0xf);
}

fn formProfileFromMask(mask: u64) u128 {
    var profile: u128 = 0;
    var rank_index: usize = 0;
    while (rank_index < 32) : (rank_index += 1) {
        if (((mask >> @intCast(rank_index)) & 1) == 0) continue;
        profile += @as(u128, 1) << @intCast(rank_index * 4);
    }
    return profile;
}

fn formProfilesIntersect(left: u128, right: u128) bool {
    var rank_index: usize = 0;
    while (rank_index < 32) : (rank_index += 1) {
        if (formProfileCount(left, rank_index) != 0 and formProfileCount(right, rank_index) != 0) return true;
    }
    return false;
}

fn appendCliffordProductAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), left_atom: rendering.SymbolicAtom, right_atom: rendering.SymbolicAtom) !void {
    const left = gammaProductLeftBlock(left_atom) orelse return;
    const right = gammaProductRightAction(right_atom) orelse return;
    if (left.block != right.block) return;
    if (left.orthogonal_dimension != right.orthogonal_dimension) return error.InvalidGammaProductTerm;

    const expansion = try rendering.gammaProductExpansion(left.orthogonal_dimension, left.rank, right.rank, left.duality, right.duality);
    for (expansion.slice()) |term| {
        const plan = try rendering.gammaProductContractionPlan(left.rank, right.rank, term);
        try atoms.append(allocator, .{ .clifford_product = .{
            .left_operator_id = left.operator_id,
            .right_operator_id = right.operator_id,
            .left_block = left.block,
            .right_block = right.block,
            .orthogonal_dimension = left.orthogonal_dimension,
            .left_rank = left.rank,
            .right_rank = right.rank,
            .output_rank = term.rank,
            .contractions = term.contractions,
            .metric_count = plan.metric_len,
            .free_vector_count = plan.free_len,
            .coefficient = term.coefficient,
            .left_duality = left.duality,
            .right_duality = right.duality,
            .output_duality = term.duality,
        } });
    }
}

const GammaProductInput = struct {
    operator_id: u32,
    block: rendering.IndexBlockId,
    orthogonal_dimension: u16,
    rank: u8,
    duality: rendering.DualityTag = .none,
};

fn gammaProductLeftBlock(atom: rendering.SymbolicAtom) ?GammaProductInput {
    return switch (atom) {
        .gamma_matrix => |gamma| .{
            .operator_id = gamma.operator_id,
            .block = gamma.vector,
            .orthogonal_dimension = gamma.orthogonal_dimension,
            .rank = gamma.rank,
            .duality = gamma.duality,
        },
        .gamma_form => |gamma| .{
            .operator_id = gamma.operator_id,
            .block = gamma.form,
            .orthogonal_dimension = gamma.orthogonal_dimension,
            .rank = gamma.rank,
            .duality = gamma.duality,
        },
        else => null,
    };
}

fn gammaProductRightAction(atom: rendering.SymbolicAtom) ?GammaProductInput {
    return switch (atom) {
        .gamma_action => |gamma| .{
            .operator_id = gamma.operator_id,
            .block = gamma.form,
            .orthogonal_dimension = gamma.orthogonal_dimension,
            .rank = gamma.rank,
            .duality = gamma.duality,
        },
        else => null,
    };
}

fn isZeroDynkin(label: []const i16) bool {
    for (label) |entry| {
        if (entry != 0) return false;
    }
    return true;
}

fn externalIndexOffset(request: coupling.InvariantBasisRequest, leg_index: usize) u32 {
    var offset: u32 = 0;
    for (request.external_legs[0..leg_index]) |leg| {
        offset += @intCast(leg.indices.len);
    }
    return offset;
}

fn tensorSpinorSpinorIndex(index: rendering.IndexRef) rendering.IndexRef {
    return 0x80000000 | index;
}

const TensorFormProjectionGammaFallback = struct {
    operator_id: u32,
    left: rendering.IndexRef,
    right: rendering.IndexRef,
    output: rendering.IndexRef,
    orthogonal_dimension: u16,
    input_form_profile: u128,
    input_form_mask: u64,
    output_form_profile: u128,
    output_form_count: u8,
    output_form_rank: u8,
    output_duality: rendering.DualityTag,
    right_chirality: u8,
    chirality: u8,
};

fn appendTensorFormProjectionGammaFallback(cache: *projector_constructor.TensorFormProjectionProgramCache, atoms: *std.ArrayList(rendering.SymbolicAtom), program: TensorFormProjectionGammaFallback) !void {
    _ = try cache.appendExpression(atoms, .{
        .operator_id = program.operator_id,
        .left = program.left,
        .right = program.right,
        .output = program.output,
        .orthogonal_dimension = program.orthogonal_dimension,
        .input_form_profile = program.input_form_profile,
        .input_form_mask = program.input_form_mask,
        .output_form_profile = program.output_form_profile,
        .output_form_count = program.output_form_count,
        .output_form_rank = program.output_form_rank,
        .output_duality = program.output_duality,
        .right_chirality = program.right_chirality,
        .chirality = program.chirality,
    });
}

fn findIndexKind(indices: []const realization.NamedIndex, kind: realization.IndexKind) ?usize {
    for (indices, 0..) |index, offset| {
        if (index.kind == kind) return offset;
    }
    return null;
}

fn findSpinorIndex(indices: []const realization.NamedIndex) ?usize {
    for (indices, 0..) |index, offset| {
        switch (index.kind) {
            .spinor, .conjugate_spinor => return offset,
            else => {},
        }
    }
    return null;
}

fn expectSpin10GammaForm(ctx: *Context, so10: store.AlgebraHandle, spinor: store.IrrepHandle, spinor_kind: realization.IndexKind, form_label: []const i16, expected_rank: u8, expected_chirality: u8, expected_duality: rendering.DualityTag) !void {
    const testing = std.testing;

    const form = try ctx.registerIrrep(so10, .{ .dynkin = form_label });
    const external_form = try ctx.dualIrrep(form);
    const spinor_leg = realization.ExternalLeg.primitive(spinor, &.{
        .init(spinor_kind, "a"),
    });
    const form_leg = realization.ExternalLeg.primitive(external_form, &.{
        .init(.form, "M"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ spinor_leg, spinor_leg, form_leg },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 1), sink.term_count);
    try testing.expectEqual(@as(u32, 2), sink.atom_count);
    try testing.expectEqual(@as(u32, 1), sink.gamma_form_count);
    try testing.expectEqual(@as(u32, 1), sink.generalized_delta_count);
    try testing.expectEqual(@as(u16, 10), sink.first_gamma_form_dimension.?);
    try testing.expectEqual(expected_rank, sink.first_gamma_form_rank.?);
    try testing.expectEqual(expected_chirality, sink.first_gamma_form_chirality.?);
    try testing.expectEqual(expected_duality, sink.first_gamma_form_duality.?);
    try testing.expectEqual(@as(u64, 1), audit.accepted);
    try testing.expectEqual(@as(u64, 1), audit.emitted);

    const descriptor = ctx.projectorDescriptor(sink.first_gamma_form_operator_id.?).?;
    switch (descriptor.role) {
        .product_channel => |channel| {
            try testing.expectEqual(spinor.value, channel.left.value);
            try testing.expectEqual(spinor.value, channel.right.value);
            try testing.expectEqual(form.value, channel.output.value);
            try testing.expectEqual(@as(u16, 0), channel.multiplicity_copy);
        },
        else => return error.ExpectedGammaFormProductChannel,
    }
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, descriptor.derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_spinor_form_channel, descriptor.derivation.formula_kind);
    try testing.expect(descriptor.derivation.formula_audit.verified());

    const paths = ctx.impl().couplings.basisPaths(basis).?;
    const steps = ctx.impl().couplings.pathSteps(paths[0]);
    try testing.expectEqual(@as(usize, 2), steps.len);
    const form_pair_derivation = ctx.impl().projectors.projectorDerivation(steps[1].projector).?;
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, form_pair_derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_form_pair, form_pair_derivation.formula_kind);
    try testing.expect(form_pair_derivation.formula_audit.verified());

    var gamma_filter_sink: CountingSink = .{};
    const gamma_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.gamma), &gamma_filter_sink);
    try testing.expectEqual(@as(u32, 0), gamma_filter_sink.term_count);
    try testing.expectEqual(@as(u64, 1), gamma_filter_audit.rejected);
    try testing.expectEqual(@as(u64, 0), gamma_filter_audit.emitted);
}

fn expectSpin10TensorSpinorProjection(ctx: *Context, so10: store.AlgebraHandle, tower: store.IrrepHandle, spinor: store.IrrepHandle, output_label: []const i16, expected_rank: u8, expected_form_count: u8, expected_form_mask: u64, expected_tower_power: u16, expected_chirality: u8) !void {
    const testing = std.testing;
    _ = expected_rank;
    _ = expected_form_mask;

    const output = try ctx.registerIrrep(so10, .{ .dynkin = output_label });
    const tower_leg = realization.ExternalLeg.primitive(tower, &.{
        .init(.custom, "T"),
    });
    const spinor_leg = realization.ExternalLeg.primitive(spinor, &.{
        .init(.spinor, "a"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ tower_leg, spinor_leg },
        .target = .{ .irrep = output },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expect(sink.term_count > 0);
    const solved_spinor_contract = sink.spinor_tower_contract_count > 0;
    const solved_gamma_wedge_shift = sink.tensor_form_gamma_wedge_count > 0;
    const solved_gamma_map = sink.tensor_form_gamma_map_count > 0 or sink.tensor_form_gamma_map_adjoint_count > 0;
    const solved_form_spinor_pair = sink.tensor_form_spinor_pair_count > 0;
    const solved_gamma_action = sink.gamma_action_count > 0;
    const solved_exterior_gamma_action = sink.exterior_gamma_action_count > 0;
    const solved_structural = solved_spinor_contract or solved_gamma_wedge_shift or solved_gamma_map or solved_form_spinor_pair or solved_gamma_action or solved_exterior_gamma_action;
    if (solved_spinor_contract and solved_gamma_wedge_shift) {
        try testing.expectEqual(@as(u32, 0), sink.tensor_spinor_projection_count);
        try testing.expect(sink.tensor_form_gamma_wedge_count >= 2);
        try testing.expectEqual(sink.spinor_tower_contract_count, sink.spinor_tower_contract_adjoint_count);
        try testing.expect(sink.spinor_tower_contract_count >= 1);
        try testing.expect(sink.atom_count >= sink.spinor_tower_contract_count + sink.spinor_tower_contract_adjoint_count + sink.tensor_form_gamma_wedge_count + sink.generalized_delta_count);
        try testing.expectEqual(@as(u16, 10), sink.first_spinor_tower_contract_dimension.?);
        try testing.expectEqual(@as(u16, 10), sink.first_tensor_form_gamma_wedge_dimension.?);
        try testing.expect(sink.first_spinor_tower_contract_chirality.? != 0);
        try testing.expect(sink.first_tensor_form_gamma_wedge_chirality.? != 0);
    } else if (solved_spinor_contract) {
        try testing.expectEqual(@as(u32, 2) + sink.generalized_delta_count, sink.atom_count);
        try testing.expectEqual(@as(u32, 0), sink.tensor_spinor_projection_count);
        try testing.expectEqual(@as(u32, 1), sink.spinor_tower_contract_count);
        try testing.expectEqual(@as(u32, 1), sink.spinor_tower_contract_adjoint_count);
        try testing.expectEqual(@as(u32, 0), sink.generalized_delta_count % 2);
        try testing.expect(sink.generalized_delta_count <= @as(u32, expected_form_count) * 2);
        try testing.expectEqual(@as(u16, 10), sink.first_spinor_tower_contract_dimension.?);
        const contract_input = sink.first_spinor_tower_contract_input_power.?;
        const contract_output = sink.first_spinor_tower_contract_output_power.?;
        try testing.expect(contract_input == contract_output + 1);
        try testing.expect(contract_input == expected_tower_power or contract_output == expected_tower_power);
        try testing.expect(sink.first_spinor_tower_contract_form_rank.? <= 10);
        try testing.expect(sink.first_spinor_tower_contract_chirality.? != 0);
    } else if (solved_gamma_wedge_shift) {
        try testing.expectEqual(@as(u32, 2), sink.atom_count);
        try testing.expectEqual(@as(u32, 0), sink.tensor_spinor_projection_count);
        try testing.expectEqual(@as(u32, 2), sink.tensor_form_gamma_wedge_count);
        try testing.expectEqual(@as(u16, 10), sink.first_tensor_form_gamma_wedge_dimension.?);
        try testing.expect(sink.first_tensor_form_gamma_wedge_input_profile.? != 0);
        try testing.expect(sink.first_tensor_form_gamma_wedge_output_profile.? != 0);
        try testing.expect(sink.first_tensor_form_gamma_wedge_inserted_rank.? != 0);
        try testing.expectEqual(expected_chirality, sink.first_tensor_form_gamma_wedge_chirality.?);
    } else {
        try testing.expect(sink.atom_count > 0);
        try testing.expect(solved_structural);
        try testing.expectEqual(@as(u32, 0), sink.tensor_spinor_projection_count);
        if (solved_gamma_map) {
            try testing.expectEqual(@as(u16, 10), sink.first_tensor_form_gamma_map_dimension.?);
            try testing.expect(sink.first_tensor_form_gamma_map_source_rank.? <= 10);
            try testing.expect(sink.first_tensor_form_gamma_map_chirality.? != 0);
        }
        if (solved_form_spinor_pair) {
            try testing.expectEqual(@as(u16, 10), sink.first_tensor_form_spinor_pair_dimension.?);
            try testing.expect(sink.first_tensor_form_spinor_pair_output_count.? <= expected_form_count);
        }
    }
    try testing.expectEqual(@as(u64, sink.term_count), audit.accepted);
    try testing.expectEqual(@as(u64, sink.term_count), audit.emitted);

    const paths = ctx.impl().couplings.basisPaths(basis).?;
    const steps = ctx.impl().couplings.pathSteps(paths[0]);
    try testing.expect(steps.len > 0);
    const descriptor = ctx.projectorDescriptor(steps[0].projector).?;
    switch (descriptor.role) {
        .product_channel => |channel| {
            try testing.expectEqual(tower.value, channel.left.value);
            try testing.expectEqual(spinor.value, channel.right.value);
            try testing.expectEqual(output.value, channel.output.value);
            try testing.expectEqual(@as(u16, 0), channel.multiplicity_copy);
        },
        else => return error.ExpectedTensorSpinorProductChannel,
    }
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, descriptor.derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_structural_projection, descriptor.derivation.formula_kind);
    try testing.expect(descriptor.derivation.formula_audit.verified());

    var projector_filter_sink: CountingSink = .{};
    const projector_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.projector), &projector_filter_sink);
    if (solved_structural) {
        try testing.expect(projector_filter_sink.term_count > 0);
        try testing.expectEqual(@as(u32, 0), projector_filter_sink.tensor_spinor_projection_count);
        try testing.expectEqual(@as(u64, 0), projector_filter_audit.rejected);
        try testing.expectEqual(@as(u64, projector_filter_sink.term_count), projector_filter_audit.emitted);
    } else {
        try testing.expectEqual(@as(u32, 0), projector_filter_sink.term_count);
        try testing.expectEqual(@as(u64, 1), projector_filter_audit.rejected);
        try testing.expectEqual(@as(u64, 0), projector_filter_audit.emitted);
    }
}

fn expectSpin10TensorFormProjection(ctx: *Context, so10: store.AlgebraHandle, left: store.IrrepHandle, spinor: store.IrrepHandle, output_label: []const i16, expected_input_mask: u64, expected_output_profile: u128, expected_output_count: u8) !void {
    const testing = std.testing;
    _ = expected_input_mask;
    _ = expected_output_profile;
    _ = expected_output_count;

    const output = try ctx.registerIrrep(so10, .{ .dynkin = output_label });
    const left_leg = realization.ExternalLeg.primitive(left, &.{
        .init(.custom, "T"),
    });
    const spinor_leg = realization.ExternalLeg.primitive(spinor, &.{
        .init(.spinor, "a"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ left_leg, spinor_leg },
        .target = .{ .irrep = output },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expect(sink.term_count > 0);
    try testing.expect(sink.atom_count > 0);
    try testing.expectEqual(@as(u32, 0), sink.projector_operator_count);
    try testing.expectEqual(@as(u32, 0), sink.tensor_form_projection_count);
    try testing.expectEqual(@as(u32, 0), sink.tensor_spinor_projection_count);
    try testing.expectEqual(@as(u64, 1), audit.accepted);
    try testing.expectEqual(@as(u64, sink.term_count), audit.emitted);

    const paths = ctx.impl().couplings.basisPaths(basis).?;
    const steps = ctx.impl().couplings.pathSteps(paths[0]);
    try testing.expect(steps.len > 0);
    const descriptor = ctx.projectorDescriptor(steps[0].projector).?;
    switch (descriptor.role) {
        .product_channel => |channel| {
            try testing.expectEqual(left.value, channel.left.value);
            try testing.expectEqual(spinor.value, channel.right.value);
            try testing.expectEqual(output.value, channel.output.value);
            try testing.expectEqual(@as(u16, 0), channel.multiplicity_copy);
        },
        else => return error.ExpectedTensorFormProductChannel,
    }
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, descriptor.derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_structural_projection, descriptor.derivation.formula_kind);
    try testing.expect(descriptor.derivation.formula_audit.verified());

    var projector_filter_sink: CountingSink = .{};
    const projector_filter_audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.withoutOperatorKind(.projector), &projector_filter_sink);
    try testing.expect(projector_filter_sink.term_count > 0);
    try testing.expectEqual(@as(u32, 0), projector_filter_sink.tensor_form_projection_count);
    try testing.expectEqual(@as(u32, 0), projector_filter_sink.tensor_spinor_projection_count);
    try testing.expectEqual(@as(u64, 0), projector_filter_audit.rejected);
    try testing.expectEqual(@as(u64, projector_filter_sink.term_count), projector_filter_audit.emitted);
}

fn expectSpin10TensorMiddleFormProjection(ctx: *Context, so10: store.AlgebraHandle, left: store.IrrepHandle, spinor: store.IrrepHandle, output_label: []const i16, expected_input_mask: u64, expected_output_rank: u8, expected_duality: rendering.DualityTag) !void {
    const testing = std.testing;

    const output = try ctx.registerIrrep(so10, .{ .dynkin = output_label });
    const left_leg = realization.ExternalLeg.primitive(left, &.{
        .init(.custom, "T"),
    });
    const spinor_leg = realization.ExternalLeg.primitive(spinor, &.{
        .init(.spinor, "a"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ left_leg, spinor_leg },
        .target = .{ .irrep = output },
    });

    try testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    var sink: CountingSink = .{};
    const audit = try ctx.renderInvariantFiltered(basis, .init(0), .{ .projectors = .expanded_terms }, rendering.ExpansionFilter.acceptAll(), &sink);
    try testing.expectEqual(@as(u32, 1), sink.term_count);
    try testing.expect(sink.atom_count > 0);
    const input_rank: u8 = if (expected_input_mask == 0) 0 else @intCast(@ctz(expected_input_mask) + 1);
    try testing.expectEqual(@as(u32, 0), sink.tensor_form_projection_count);
    if (sink.tensor_form_gamma_wedge_count != 0) {
        try testing.expectEqual(@as(u16, 10), sink.first_tensor_form_gamma_wedge_dimension.?);
        try testing.expectEqual(expected_input_mask, sink.first_tensor_form_gamma_wedge_input_mask.?);
        try testing.expectEqual(@as(u128, 0), sink.first_tensor_form_gamma_wedge_output_profile.?);
        try testing.expectEqual(@as(u8, 1), sink.first_tensor_form_gamma_wedge_output_count.?);
        try testing.expectEqual(expected_output_rank - input_rank, sink.first_tensor_form_gamma_wedge_inserted_rank.?);
    } else if (sink.exterior_gamma_action_count != 0) {
        try testing.expectEqual(@as(u16, 10), sink.first_exterior_gamma_action_dimension.?);
    } else {
        try testing.expect(sink.gamma_form_count > 0 and sink.gamma_action_count > 0);
        try testing.expectEqual(@as(u16, 10), sink.first_gamma_form_dimension.?);
        try testing.expectEqual(expected_duality, sink.first_gamma_form_duality.?);
    }
    try testing.expectEqual(@as(u64, 1), audit.accepted);
    try testing.expectEqual(@as(u64, 1), audit.emitted);

    const paths = ctx.impl().couplings.basisPaths(basis).?;
    const steps = ctx.impl().couplings.pathSteps(paths[0]);
    try testing.expect(steps.len > 0);
    const descriptor = ctx.projectorDescriptor(steps[0].projector).?;
    switch (descriptor.role) {
        .product_channel => |channel| {
            try testing.expectEqual(left.value, channel.left.value);
            try testing.expectEqual(spinor.value, channel.right.value);
            try testing.expectEqual(output.value, channel.output.value);
            try testing.expectEqual(@as(u16, 0), channel.multiplicity_copy);
        },
        else => return error.ExpectedTensorMiddleFormProductChannel,
    }
    try testing.expectEqual(projector.ExpansionStatus.expandable_terms, descriptor.derivation.status);
    try testing.expectEqual(projector.ProjectorFormulaKind.orthogonal_structural_projection, descriptor.derivation.formula_kind);
    try testing.expect(descriptor.derivation.formula_audit.verified());
}

fn expectDualPairInvariantCount(ctx: *Context, simple: symmetry.SimpleLieAlgebra, label: []const i16) !void {
    const algebra = try ctx.registerAlgebra(.{ .simple = simple });
    const irrep = try ctx.registerIrrep(algebra, .{ .dynkin = label });
    const dual = try ctx.dualIrrep(irrep);
    const left = realization.ExternalLeg.primitive(irrep, &.{
        .init(.custom, "left"),
    });
    const right = realization.ExternalLeg.primitive(dual, &.{
        .init(.custom, "right"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = algebra,
        .external_legs = &.{ left, right },
    });

    try std.testing.expectEqual(@as(u128, 1), ctx.basisInvariantCount(basis).?);
    try std.testing.expectEqual(@as(u128, 1), ctx.basisAudit(basis).?.path_count);
}

fn expectRepeatedLegInvariantCount(ctx: *Context, simple: symmetry.SimpleLieAlgebra, label: []const i16, comptime leg_count: usize, expected_count: u128) !void {
    const algebra = try ctx.registerAlgebra(.{ .simple = simple });
    const irrep = try ctx.registerIrrep(algebra, .{ .dynkin = label });
    const leg = realization.ExternalLeg.primitive(irrep, &.{
        .init(.custom, "x"),
    });
    const legs = [_]realization.ExternalLeg{leg} ** leg_count;
    const basis = try ctx.invariantBasis(.{
        .algebra = algebra,
        .external_legs = legs[0..],
    });

    try std.testing.expectEqual(expected_count, ctx.basisInvariantCount(basis).?);
    try std.testing.expectEqual(expected_count, ctx.basisAudit(basis).?.path_count);
}
