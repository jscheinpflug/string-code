const coupling = @import("coupling.zig");
const realization = @import("realization.zig");
const store = @import("representation-store.zig");
const symmetry = @import("symmetry.zig");

/// TensorExprId names a tensor expression stored by tensor-code.
pub const TensorExprId = u32;
/// TensorTermId names one term inside a tensor expression store.
const TensorTermId = u32;
/// BasisPathId names one compact coupling path in an invariant basis.
const BasisPathId = u32;
/// RenderedTermId names one streamed symbolic tensor term.
const RenderedTermId = u32;
/// ReductionTermId names one coefficient in a target invariant basis.
const ReductionTermId = u32;
/// InvariantFamilyId names a family of invariant tensor candidates.
const InvariantFamilyId = u16;
/// AlgebraSchemaId names a Lie or superalgebra schema.
const AlgebraSchemaId = u16;
/// GradingId names a grading attached to a tensor algebra schema.
const GradingId = u16;

/// TensorExprSource streams tensor expression ids from a generator.
const TensorExprSource = struct {
    next_fn: *const fn (*anyopaque) ?TensorExprId,
    state: *anyopaque,

    /// next returns the next generated tensor expression id.
    pub fn next(self: *TensorExprSource) ?TensorExprId {
        return self.next_fn(self.state);
    }
};

/// BasisPathSource streams invariant ids from a generated basis.
const BasisPathSource = struct {
    next_fn: *const fn (*anyopaque) ?coupling.InvariantHandle,
    state: *anyopaque,

    /// next returns the next invariant in the basis.
    pub fn next(self: *BasisPathSource) ?coupling.InvariantHandle {
        return self.next_fn(self.state);
    }
};

/// RenderedTermSource streams symbolic terms for one invariant rendering.
const RenderedTermSource = struct {
    next_fn: *const fn (*anyopaque) ?RenderedTermId,
    state: *anyopaque,

    /// next returns the next rendered symbolic term.
    pub fn next(self: *RenderedTermSource) ?RenderedTermId {
        return self.next_fn(self.state);
    }
};

/// ReductionTermSource streams coefficients in a chosen invariant basis.
const ReductionTermSource = struct {
    next_fn: *const fn (*anyopaque) ?ReductionTermId,
    state: *anyopaque,

    /// next returns the next reduction coefficient term.
    pub fn next(self: *ReductionTermSource) ?ReductionTermId {
        return self.next_fn(self.state);
    }
};

/// InvariantFamily declares the tensor-invariant problem to generate.
const InvariantFamily = struct {
    name: []const u8,
    algebra: AlgebraSchemaId,
    external_representations: []const symmetry.RepresentationId,
};

/// InvariantRequest records a named public invariant-basis request.
const InvariantRequest = struct {
    name: []const u8,
    algebra: store.AlgebraHandle,
    external_legs: []const realization.ExternalLeg,
    target: coupling.TargetIrrep = .singlet,
    tree_policy: coupling.TreePolicy = .auto,
    basis_policy: coupling.BasisPolicy = .default,
};

/// AlgebraSchema records the compact tensor data of a symmetry algebra.
const AlgebraSchema = struct {
    name: []const u8,
    symmetry: symmetry.SymmetryId,
    grading: ?GradingId = null,
    metric: ?TensorExprId = null,
    structure_constants: ?TensorExprId = null,
};
