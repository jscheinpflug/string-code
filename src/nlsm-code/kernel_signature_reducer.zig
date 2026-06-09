const std = @import("std");
const geometry = @import("local_geometry_reducer.zig");
const counterterms = @import("counterterms.zig");
const plan = @import("diagram_plan.zig");
const pair = @import("pairing_engine.zig");
const pole = @import("pole_extractor.zig");
const rnc = @import("rnc_vertices.zig");
const scheme = @import("scheme.zig");

/// KernelReductionRequest fixes the renormalization metadata attached to emitted kernel rows.
pub const KernelReductionRequest = struct {
    scheme: scheme.DimRegMS,
    local_operator: counterterms.LocalCountertermKind,
    target_flavor: geometry.GeometryFlavor = .generic_riemannian,
    alpha_prime_power: i16 = 0,
};

/// KernelReductionSummary reports how many candidates were lowered successfully.
pub const KernelReductionSummary = struct {
    emitted_count: usize = 0,
    unsupported_tensor_count: u32 = 0,
};

fn productKernelFamily(candidate: plan.DiagramCandidateRow) counterterms.KernelFamily {
    return switch (candidate.loop_order) {
        0 => .scaleless_tadpole,
        1 => .bubble,
        2 => .nested_bubble,
        3 => .sunset,
        else => .vacuum,
    };
}

fn loopKernelFamily(loop_order: u8) counterterms.KernelFamily {
    return switch (loop_order) {
        0 => .scaleless_tadpole,
        1 => .bubble,
        2 => .nested_bubble,
        3 => .sunset,
        else => .vacuum,
    };
}

fn appendTensorAtom(
    tensor: rnc.VertexTensor,
    atoms: []geometry.TensorAtom,
    atom_count: *usize,
    slots: []geometry.TensorSlot,
    slot_count: *usize,
    next_slot_id: *u32,
) !void {
    if (atom_count.* == atoms.len) return error.AtomScratchTooSmall;

    const slot_start = slot_count.*;
    if (slot_start + tensor.slot_sorts.len > slots.len) return error.SlotScratchTooSmall;

    for (tensor.slot_sorts, 0..) |sort, offset| {
        slots[slot_start + offset] = .{
            .id = next_slot_id.*,
            .sort = sort,
        };
        next_slot_id.* += 1;
    }
    slot_count.* += tensor.slot_sorts.len;

    switch (tensor.kind) {
        .metric => {
            atoms[atom_count.*] = .{
                .kind = .metric,
                .slots = slots[slot_start .. slot_start + tensor.slot_sorts.len],
            };
        },
        .riemann => {
            atoms[atom_count.*] = .{
                .kind = .riemann,
                .slots = slots[slot_start .. slot_start + tensor.slot_sorts.len],
            };
        },
        .covariant_derivative_riemann => {
            const derivative_start = slot_count.*;
            if (derivative_start + tensor.covariant_derivative_count > slots.len) return error.SlotScratchTooSmall;
            const derivative_sort = if (tensor.slot_sorts.len == 0) geometry.TensorSlotSort.real_tangent else tensor.slot_sorts[0];
            for (0..tensor.covariant_derivative_count) |_| {
                slots[slot_count.*] = .{
                    .id = next_slot_id.*,
                    .sort = derivative_sort,
                };
                next_slot_id.* += 1;
                slot_count.* += 1;
            }

            atoms[atom_count.*] = .{
                .kind = .covariant_derivative,
                .slots = slots[slot_start .. slot_start + tensor.slot_sorts.len],
                .derivative_slots = slots[derivative_start .. derivative_start + tensor.covariant_derivative_count],
            };
        },
    }

    atom_count.* += 1;
}

fn vertexFactor(row: rnc.RncVertexRow) counterterms.Rational {
    return .{
        .numerator = row.coefficient,
        .denominator = row.symmetry.denominator,
    };
}

fn accumulateVertexTensors(
    catalog: []const rnc.RncVertexRow,
    vertices: []const plan.VertexMultiplicity,
    atoms: []geometry.TensorAtom,
    slots: []geometry.TensorSlot,
    atom_count: *usize,
    slot_count: *usize,
    next_slot_id: *u32,
    combinatorial: *counterterms.Rational,
    automorphism_denominator: u32,
) !void {
    combinatorial.* = .{ .numerator = 1, .denominator = automorphism_denominator };

    for (vertices) |entry| {
        const row = catalog[entry.vertex_index];
        const factor = vertexFactor(row);

        var repeat_index: u8 = 0;
        while (repeat_index < entry.multiplicity) : (repeat_index += 1) {
            combinatorial.* = try combinatorial.*.mul(factor);
            for (row.tensors) |tensor| try appendTensorAtom(tensor, atoms, atom_count, slots, slot_count, next_slot_id);
        }
    }
}

fn branchKernelSignature(branch: pair.PairingBranchRow) counterterms.KernelSignature {
    const pair_total = branch.kernel_factors.len;
    const propagator_len: u8 = @intCast(@min(pair_total * 2, 8));
    var propagator_powers = [_]u8{0} ** 8;
    var primitive_pair_histogram = [_]u8{0} ** 8;
    var numerator_rank: u8 = 0;

    for (branch.kernel_factors, 0..) |factor, index| {
        const slot = index * 2;
        if (slot < propagator_powers.len) propagator_powers[slot] = factor.propagator_power;
        if (slot + 1 < propagator_powers.len) propagator_powers[slot + 1] = factor.propagator_power;
        const kind_index = @intFromEnum(factor.kind);
        if (kind_index < primitive_pair_histogram.len) primitive_pair_histogram[kind_index] +|= 1;
        numerator_rank +|= factor.numerator_rank;
    }

    return .{
        .family = loopKernelFamily(branch.loop_order),
        .loop_order = branch.loop_order,
        .propagator_len = propagator_len,
        .propagator_powers = propagator_powers,
        .primitive_pair_histogram = primitive_pair_histogram,
        .numerator_rank = numerator_rank,
        .external_derivative_order = branch.background.d_x0 + branch.background.dbar_x0,
    };
}

/// streamKernelTerms lowers candidate vertex multisets to reduced kernel-signature rows.
pub fn streamKernelTerms(
    request: KernelReductionRequest,
    catalog: []const rnc.RncVertexRow,
    candidates: []const plan.DiagramCandidateRow,
    sink: anytype,
    scratch_atoms: []geometry.TensorAtom,
    scratch_slots: []geometry.TensorSlot,
) !KernelReductionSummary {
    var summary = KernelReductionSummary{};

    for (candidates) |candidate| {
        var atom_count: usize = 0;
        var slot_count: usize = 0;
        var next_slot_id: u32 = 1;
        var combinatorial = counterterms.Rational{};
        try accumulateVertexTensors(catalog, candidate.vertices, scratch_atoms, scratch_slots, &atom_count, &slot_count, &next_slot_id, &combinatorial, candidate.automorphism_denominator);

        const propagator_len: u8 = @intCast(@min(candidate.internal_propagator_count * 2, 8));
        var propagator_powers = [_]u8{0} ** 8;
        for (0..propagator_len) |index| propagator_powers[index] = 1;

        try sink.emit(.{
            .scheme = request.scheme,
            .local_operator = request.local_operator,
            .target_flavor = request.target_flavor,
            .alpha_prime_power = request.alpha_prime_power,
            .combinatorial = combinatorial.normalized(),
            .kernel = .{
                .family = productKernelFamily(candidate),
                .loop_order = candidate.loop_order,
                .propagator_len = propagator_len,
                .propagator_powers = propagator_powers,
                .numerator_rank = @intCast(candidate.total_fermion_field_count),
                .external_derivative_order = candidate.background.d_x0 + candidate.background.dbar_x0,
            },
            .term = .{
                .atoms = scratch_atoms[0..atom_count],
            },
        });
        summary.emitted_count += 1;
    }

    return summary;
}

/// streamKernelTermsFromPairingBranches lowers explicit pairing branches to reduced kernel rows.
pub fn streamKernelTermsFromPairingBranches(
    request: KernelReductionRequest,
    catalog: []const rnc.RncVertexRow,
    branches: []const pair.PairingBranchRow,
    sink: anytype,
    scratch_atoms: []geometry.TensorAtom,
    scratch_slots: []geometry.TensorSlot,
) !KernelReductionSummary {
    var summary = KernelReductionSummary{};

    for (branches) |branch| {
        var atom_count: usize = 0;
        var slot_count: usize = 0;
        var next_slot_id: u32 = 1;
        var combinatorial = counterterms.Rational{};
        try accumulateVertexTensors(catalog, branch.vertices, scratch_atoms, scratch_slots, &atom_count, &slot_count, &next_slot_id, &combinatorial, branch.automorphism_denominator);

        const pair_total = branch.boson_pair_count + branch.left_fermion_pair_count + branch.right_fermion_pair_count;
        std.debug.assert(pair_total == branch.kernel_factors.len);

        try sink.emit(.{
            .scheme = request.scheme,
            .local_operator = request.local_operator,
            .target_flavor = request.target_flavor,
            .alpha_prime_power = request.alpha_prime_power,
            .combinatorial = combinatorial.normalized(),
            .kernel = branchKernelSignature(branch),
            .term = .{
                .atoms = scratch_atoms[0..atom_count],
            },
        });
        summary.emitted_count += 1;
    }

    return summary;
}

test "kernel reducer lowers the one-loop bosonic metric candidate to a bubble row" {
    const testing = std.testing;
    const CandidateSink = struct {
        rows: []plan.DiagramCandidateRow,
        vertex_storage: []plan.VertexMultiplicity,
        count: usize = 0,
        vertex_offset: usize = 0,

        pub fn emit(self: *@This(), row: plan.DiagramCandidateRow) !void {
            const start = self.vertex_offset;
            const end = start + row.vertices.len;
            std.mem.copyForwards(plan.VertexMultiplicity, self.vertex_storage[start..end], row.vertices);
            self.rows[self.count] = row;
            self.rows[self.count].vertices = self.vertex_storage[start..end];
            self.count += 1;
            self.vertex_offset = end;
        }
    };

    const VertexSink = struct {
        rows: []rnc.RncVertexRow,
        count: usize = 0,

        pub fn emit(self: *@This(), row: rnc.RncVertexRow) !void {
            self.rows[self.count] = row;
            self.count += 1;
        }
    };

    const KernelSink = struct {
        rows: []pole.KernelTermRow,
        count: usize = 0,

        pub fn emit(self: *@This(), row: pole.KernelTermRow) !void {
            self.rows[self.count] = row;
            self.count += 1;
        }
    };

    var catalog_storage: [4]rnc.RncVertexRow = undefined;
    var vertex_sink = VertexSink{ .rows = &catalog_storage };
    try rnc.streamBootstrapVertices(.{ .worldsheet = .bosonic, .max_xi_order = 2, .include_fermions = false }, &vertex_sink);
    const catalog = catalog_storage[0..vertex_sink.count];

    var candidate_storage: [4]plan.DiagramCandidateRow = undefined;
    var candidate_vertex_storage: [4]plan.VertexMultiplicity = undefined;
    var candidate_sink = CandidateSink{ .rows = &candidate_storage, .vertex_storage = &candidate_vertex_storage };
    var multiplicities: [4]u8 = undefined;
    var vertices: [4]plan.VertexMultiplicity = undefined;
    try plan.streamDiagramCandidates(.{
        .worldsheet = .bosonic,
        .loop_order = 1,
        .max_vertices = 1,
        .required_background = .{ .d_x0 = 1, .dbar_x0 = 1 },
        .include_fermions = false,
    }, catalog, &candidate_sink, &multiplicities, &vertices);

    var kernel_storage: [2]pole.KernelTermRow = undefined;
    var kernel_sink = KernelSink{ .rows = &kernel_storage };
    var atoms: [8]geometry.TensorAtom = undefined;
    var slots: [32]geometry.TensorSlot = undefined;
    const summary = try streamKernelTerms(.{
        .scheme = scheme.stringbookMS(),
        .local_operator = .metric_beta,
        .alpha_prime_power = 1,
    }, catalog, candidate_storage[0..candidate_sink.count], &kernel_sink, &atoms, &slots);

    try testing.expectEqual(@as(usize, 1), summary.emitted_count);
    try testing.expectEqual(counterterms.KernelFamily.bubble, kernel_storage[0].kernel.family);
    try testing.expectEqual(counterterms.Rational{ .numerator = 1, .denominator = 3 }, kernel_storage[0].combinatorial);
    try testing.expectEqual(@as(usize, 1), kernel_storage[0].term.atoms.len);
}

test "kernel reducer preserves calabi-yau flavor and rational combinatorics" {
    const testing = std.testing;
    const candidate_vertices = [_]plan.VertexMultiplicity{
        .{ .vertex_index = 0, .multiplicity = 2 },
    };
    const candidate = [_]plan.DiagramCandidateRow{.{
        .worldsheet = .n1_1,
        .vertex_count = 2,
        .distinct_vertex_count = 1,
        .internal_propagator_count = 2,
        .loop_order = 1,
        .total_quantum_field_count = 4,
        .total_fermion_field_count = 0,
        .background = .{ .d_x0 = 2, .dbar_x0 = 2 },
        .automorphism_denominator = 2,
        .vertices = &candidate_vertices,
    }};

    const real = geometry.TensorSlotSort.real_tangent;
    const tensor_sorts = [_]geometry.TensorSlotSort{ real, real, real, real };
    const background = [_]rnc.BackgroundLeg{
        .{ .kind = .d_x0, .target_sort = real },
        .{ .kind = .dbar_x0, .target_sort = real },
    };
    const fields = [_]rnc.VertexField{
        .{ .kind = .xi, .target_sort = real },
        .{ .kind = .xi, .target_sort = real },
    };
    const tensors = [_]rnc.VertexTensor{
        .{ .kind = .riemann, .slot_sorts = &tensor_sorts },
    };
    const catalog = [_]rnc.RncVertexRow{.{
        .worldsheet = .n1_1,
        .xi_order = 2,
        .fields = &fields,
        .background_legs = &background,
        .tensors = &tensors,
        .coefficient = 2,
        .symmetry = .{ .denominator = 3 },
    }};

    const Sink = struct {
        row: ?pole.KernelTermRow = null,
        pub fn emit(self: *@This(), value: pole.KernelTermRow) !void {
            self.row = value;
        }
    };

    var sink = Sink{};
    var atoms: [8]geometry.TensorAtom = undefined;
    var slots: [32]geometry.TensorSlot = undefined;
    _ = try streamKernelTerms(.{
        .scheme = scheme.stringbookMS(),
        .local_operator = .kahler_potential_beta,
        .target_flavor = .calabi_yau,
        .alpha_prime_power = 3,
    }, &catalog, &candidate, &sink, &atoms, &slots);

    try testing.expect(sink.row != null);
    try testing.expectEqual(geometry.GeometryFlavor.calabi_yau, sink.row.?.target_flavor);
    try testing.expectEqual(counterterms.Rational{ .numerator = 2, .denominator = 9 }, sink.row.?.combinatorial);
}

test "one-loop bootstrap pipeline reaches a beta row" {
    const testing = std.testing;
    const beta = @import("beta_assembly.zig");

    const VertexSink = struct {
        rows: []rnc.RncVertexRow,
        count: usize = 0,

        pub fn emit(self: *@This(), row: rnc.RncVertexRow) !void {
            self.rows[self.count] = row;
            self.count += 1;
        }
    };

    const CandidateSink = struct {
        rows: []plan.DiagramCandidateRow,
        vertex_storage: []plan.VertexMultiplicity,
        count: usize = 0,
        vertex_offset: usize = 0,

        pub fn emit(self: *@This(), row: plan.DiagramCandidateRow) !void {
            const start = self.vertex_offset;
            const end = start + row.vertices.len;
            std.mem.copyForwards(plan.VertexMultiplicity, self.vertex_storage[start..end], row.vertices);
            self.rows[self.count] = row;
            self.rows[self.count].vertices = self.vertex_storage[start..end];
            self.count += 1;
            self.vertex_offset = end;
        }
    };

    const PairingSink = struct {
        rows: []pair.PairingBranchRow,
        pair_storage: []pair.PairingEntry,
        kernel_storage: []pair.PairKernelFactor,
        count: usize = 0,
        pair_offset: usize = 0,
        kernel_offset: usize = 0,

        pub fn emit(self: *@This(), row: pair.PairingBranchRow) !void {
            const pair_start = self.pair_offset;
            const pair_end = pair_start + row.pairs.len;
            const kernel_start = self.kernel_offset;
            const kernel_end = kernel_start + row.kernel_factors.len;
            std.mem.copyForwards(pair.PairingEntry, self.pair_storage[pair_start..pair_end], row.pairs);
            std.mem.copyForwards(pair.PairKernelFactor, self.kernel_storage[kernel_start..kernel_end], row.kernel_factors);
            self.rows[self.count] = row;
            self.rows[self.count].pairs = self.pair_storage[pair_start..pair_end];
            self.rows[self.count].kernel_factors = self.kernel_storage[kernel_start..kernel_end];
            self.count += 1;
            self.pair_offset = pair_end;
            self.kernel_offset = kernel_end;
        }
    };

    const KernelSink = struct {
        rows: []pole.KernelTermRow,
        count: usize = 0,

        pub fn emit(self: *@This(), row: pole.KernelTermRow) !void {
            self.rows[self.count] = row;
            self.count += 1;
        }
    };

    var catalog_storage: [4]rnc.RncVertexRow = undefined;
    var vertex_sink = VertexSink{ .rows = &catalog_storage };
    try rnc.streamBootstrapVertices(.{ .worldsheet = .bosonic, .max_xi_order = 2, .include_fermions = false }, &vertex_sink);
    const catalog = catalog_storage[0..vertex_sink.count];

    var candidate_storage: [4]plan.DiagramCandidateRow = undefined;
    var candidate_vertex_storage: [4]plan.VertexMultiplicity = undefined;
    var candidate_sink = CandidateSink{ .rows = &candidate_storage, .vertex_storage = &candidate_vertex_storage };
    var multiplicities: [4]u8 = undefined;
    var vertices: [4]plan.VertexMultiplicity = undefined;
    try plan.streamDiagramCandidates(.{
        .worldsheet = .bosonic,
        .loop_order = 1,
        .max_vertices = 1,
        .required_background = .{ .d_x0 = 1, .dbar_x0 = 1 },
        .include_fermions = false,
    }, catalog, &candidate_sink, &multiplicities, &vertices);

    var branch_storage: [2]pair.PairingBranchRow = undefined;
    var pair_storage: [2]pair.PairingEntry = undefined;
    var kernel_factor_storage: [2]pair.PairKernelFactor = undefined;
    var pairing_sink = PairingSink{ .rows = &branch_storage, .pair_storage = &pair_storage, .kernel_storage = &kernel_factor_storage };
    var occurrences: [8]pair.PairingOccurrence = undefined;
    var species_ids: [8]u16 = undefined;
    var branch_pairs: [4]pair.PairingEntry = undefined;
    var branch_kernel_factors: [4]pair.PairKernelFactor = undefined;
    var used: [8]bool = undefined;
    const pairing_summary = try pair.streamPairingBranches(catalog, candidate_storage[0..candidate_sink.count], &pairing_sink, &occurrences, &species_ids, &branch_pairs, &branch_kernel_factors, &used);
    try testing.expectEqual(@as(usize, 1), pairing_summary.emitted_count);

    var kernel_storage: [2]pole.KernelTermRow = undefined;
    var kernel_sink = KernelSink{ .rows = &kernel_storage };
    var atoms: [8]geometry.TensorAtom = undefined;
    var slots: [32]geometry.TensorSlot = undefined;
    _ = try streamKernelTermsFromPairingBranches(.{
        .scheme = scheme.stringbookMS(),
        .local_operator = .metric_beta,
        .alpha_prime_power = 1,
    }, catalog, branch_storage[0..pairing_sink.count], &kernel_sink, &atoms, &slots);

    var poles: [2]counterterms.PoleRow = undefined;
    const pole_summary = try pole.extractPoleRows(kernel_storage[0..kernel_sink.count], pole.stringbookBootstrapRules(), &poles);
    try testing.expectEqual(@as(usize, 1), pole_summary.emitted_pole_count);

    var beta_rows: [2]counterterms.BetaRow = undefined;
    const beta_summary = try beta.assembleBetaRows(poles[0..pole_summary.emitted_pole_count], .{ .local_operator = .metric_beta }, &beta_rows);
    try testing.expectEqual(@as(usize, 1), beta_summary.beta_count);
    try testing.expectEqual(counterterms.Rational{ .numerator = 1, .denominator = 3 }, beta_rows[0].coefficient);
    try testing.expectEqual(@as(u8, 0), kernel_storage[0].kernel.numerator_rank);
}
