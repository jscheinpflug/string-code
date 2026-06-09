const std = @import("std");
const cft = @import("cft-code");
const cft_pair = @import("cft-code").PrimitivePairKernels;
const geometry = @import("local_geometry_reducer.zig");
const plan = @import("diagram_plan.zig");
const rnc = @import("rnc_vertices.zig");

/// PairSpecies identifies one independently pairable quantum field species.
pub const PairSpecies = enum(u8) {
    boson,
    left_fermion,
    right_fermion,
};

/// PairingOccurrence is one flattened quantum field occurrence in a candidate multiset.
pub const PairingOccurrence = struct {
    occurrence_id: u16,
    species: PairSpecies,
    source_vertex_index: u16,
    field_index: u8,
    derivatives: rnc.WorldsheetDerivatives = .{},
};

/// PairingEntry is one explicit field pairing inside a branch.
pub const PairingEntry = struct {
    left_occurrence: u16,
    right_occurrence: u16,
    species: PairSpecies,
    derivative_weight: u8 = 0,
};

/// PairKernelKind names the primitive free propagator carried by one pair.
pub const PairKernelKind = enum(u8) {
    xi_xi,
    d_xi_xi,
    dbar_xi_xi,
    d_xi_d_xi,
    dbar_xi_dbar_xi,
    psi_left_psi_left,
    psi_right_psi_right,
};

/// PairKernelFactor records the local kernel contribution of one explicit pair.
pub const PairKernelFactor = struct {
    kind: PairKernelKind,
    propagator_power: u8 = 1,
    derivative_order: u8 = 0,
    numerator_rank: u8 = 0,
};

/// PairingBranchRow is one explicit pairing branch before kernel reduction.
pub const PairingBranchRow = struct {
    worldsheet: rnc.WorldsheetModel,
    loop_order: u8,
    background: plan.BackgroundLegCount,
    branch_sign: i8 = 1,
    automorphism_denominator: u32 = 1,
    boson_pair_count: u16 = 0,
    left_fermion_pair_count: u16 = 0,
    right_fermion_pair_count: u16 = 0,
    derivative_pair_weight: u16 = 0,
    vertices: []const plan.VertexMultiplicity = &.{},
    pairs: []const PairingEntry = &.{},
    kernel_factors: []const PairKernelFactor = &.{},
};

/// PairingSummary reports how many explicit pairing branches were emitted.
pub const PairingSummary = struct {
    emitted_count: usize = 0,
    rejected_unpaired_count: u32 = 0,
    rejected_auxiliary_count: u32 = 0,
};

fn fieldSpecies(field: rnc.VertexField) !PairSpecies {
    return switch (field.kind) {
        .xi => .boson,
        .psi_left => .left_fermion,
        .psi_right => .right_fermion,
        .auxiliary => error.UnsupportedAuxiliaryField,
    };
}

fn derivativeWeight(occurrence: PairingOccurrence) u8 {
    return occurrence.derivatives.holomorphic + occurrence.derivatives.antiholomorphic;
}

fn derivativeProfile(derivatives: rnc.WorldsheetDerivatives) cft_pair.DerivativeProfile {
    return .{
        .holomorphic = derivatives.holomorphic,
        .antiholomorphic = derivatives.antiholomorphic,
    };
}

fn classifyBosonKernel(left: PairingOccurrence, right: PairingOccurrence) ?PairKernelFactor {
    const kernel = cft_pair.classifyFreeBosonSphereKernel(derivativeProfile(left.derivatives), derivativeProfile(right.derivatives)) orelse return null;
    return switch (kernel) {
        .x_x_logarithm => .{ .kind = .xi_xi },
        .d_x_x_logarithm => .{ .kind = .d_xi_xi, .numerator_rank = 1 },
        .d_xt_x_logarithm => .{ .kind = .dbar_xi_xi, .numerator_rank = 1 },
        .d_x_d_x_pole => .{ .kind = .d_xi_d_xi, .numerator_rank = 2 },
        .d_xt_d_xt_pole => .{ .kind = .dbar_xi_dbar_xi, .numerator_rank = 2 },
    };
}

fn classifyPairKernel(left: PairingOccurrence, right: PairingOccurrence, species: PairSpecies) ?PairKernelFactor {
    return switch (species) {
        .boson => classifyBosonKernel(left, right),
        .left_fermion => {
            const kernel = cft_pair.classifyFreeFermionSphereKernel(false, derivativeProfile(left.derivatives), derivativeProfile(right.derivatives)) orelse return null;
            return .{
                .kind = .psi_left_psi_left,
                .derivative_order = kernel.derivative_total,
                .numerator_rank = 1 + kernel.derivative_total,
            };
        },
        .right_fermion => {
            const kernel = cft_pair.classifyFreeFermionSphereKernel(true, derivativeProfile(left.derivatives), derivativeProfile(right.derivatives)) orelse return null;
            return .{
                .kind = .psi_right_psi_right,
                .derivative_order = kernel.derivative_total,
                .numerator_rank = 1 + kernel.derivative_total,
            };
        },
    };
}

fn firstUnused(used: []const bool) ?usize {
    for (used, 0..) |flag, index| {
        if (!flag) return index;
    }
    return null;
}

fn enumerateSpeciesPairings(
    occurrences: []const PairingOccurrence,
    ids: []const u16,
    used: []bool,
    species: PairSpecies,
    pairs: []PairingEntry,
    kernel_factors: []PairKernelFactor,
    pair_count: *usize,
    derivative_pair_weight: *u16,
    comptime NextCtx: type,
    next_fn: fn (*NextCtx, *usize, *u16) anyerror!void,
    next_ctx: *NextCtx,
) !void {
    const start = firstUnused(used) orelse return next_fn(next_ctx, pair_count, derivative_pair_weight);
    used[start] = true;
    defer used[start] = false;

    var partner = start + 1;
    while (partner < ids.len) : (partner += 1) {
        if (used[partner]) continue;
        used[partner] = true;
        defer used[partner] = false;

        const left = occurrences[ids[start]];
        const right = occurrences[ids[partner]];
        if (pair_count.* == pairs.len) return error.PairScratchTooSmall;
        if (pair_count.* == kernel_factors.len) return error.KernelFactorScratchTooSmall;

        const weight = derivativeWeight(left) + derivativeWeight(right);
        const factor = classifyPairKernel(left, right, species) orelse continue;
        pairs[pair_count.*] = .{
            .left_occurrence = left.occurrence_id,
            .right_occurrence = right.occurrence_id,
            .species = species,
            .derivative_weight = weight,
        };
        kernel_factors[pair_count.*] = factor;
        pair_count.* += 1;
        derivative_pair_weight.* += weight;
        try enumerateSpeciesPairings(occurrences, ids, used, species, pairs, kernel_factors, pair_count, derivative_pair_weight, NextCtx, next_fn, next_ctx);
        derivative_pair_weight.* -= weight;
        pair_count.* -= 1;
    }
}

/// streamPairingBranches enumerates admissible explicit pairings for candidate multisets.
pub fn streamPairingBranches(
    catalog: []const rnc.RncVertexRow,
    candidates: []const plan.DiagramCandidateRow,
    sink: anytype,
    scratch_occurrences: []PairingOccurrence,
    scratch_species_ids: []u16,
    scratch_pairs: []PairingEntry,
    scratch_kernel_factors: []PairKernelFactor,
    scratch_used: []bool,
) !PairingSummary {
    var summary = PairingSummary{};

    for (candidates) |candidate| {
        if (scratch_occurrences.len < candidate.total_quantum_field_count) return error.OccurrenceScratchTooSmall;
        if (scratch_species_ids.len < candidate.total_quantum_field_count) return error.SpeciesScratchTooSmall;
        if (scratch_pairs.len < candidate.total_quantum_field_count / 2) return error.PairScratchTooSmall;
        if (scratch_kernel_factors.len < candidate.total_quantum_field_count / 2) return error.KernelFactorScratchTooSmall;
        if (scratch_used.len < candidate.total_quantum_field_count) return error.UsedScratchTooSmall;

        var occurrence_count: usize = 0;
        var has_auxiliary = false;

        for (candidate.vertices) |entry| {
            const row = catalog[entry.vertex_index];
            var repeat_index: u8 = 0;
            while (repeat_index < entry.multiplicity) : (repeat_index += 1) {
                for (row.fields, 0..) |field, field_index| {
                    const species = fieldSpecies(field) catch {
                        has_auxiliary = true;
                        break;
                    };
                    scratch_occurrences[occurrence_count] = .{
                        .occurrence_id = @intCast(occurrence_count),
                        .species = species,
                        .source_vertex_index = entry.vertex_index,
                        .field_index = @intCast(field_index),
                        .derivatives = field.derivatives,
                    };
                    occurrence_count += 1;
                }
                if (has_auxiliary) break;
            }
            if (has_auxiliary) break;
        }

        if (has_auxiliary) {
            summary.rejected_auxiliary_count += 1;
            continue;
        }

        var boson_count: usize = 0;
        var left_count: usize = 0;
        var right_count: usize = 0;

        for (scratch_occurrences[0..occurrence_count]) |occurrence| switch (occurrence.species) {
            .boson => boson_count += 1,
            .left_fermion => left_count += 1,
            .right_fermion => right_count += 1,
        };

        if (boson_count % 2 != 0 or left_count % 2 != 0 or right_count % 2 != 0) {
            summary.rejected_unpaired_count += 1;
            continue;
        }

        var boson_offset: usize = 0;
        var left_offset: usize = boson_count;
        var right_offset: usize = boson_count + left_count;
        for (scratch_occurrences[0..occurrence_count], 0..) |occurrence, index| switch (occurrence.species) {
            .boson => {
                scratch_species_ids[boson_offset] = @intCast(index);
                boson_offset += 1;
            },
            .left_fermion => {
                scratch_species_ids[left_offset] = @intCast(index);
                left_offset += 1;
            },
            .right_fermion => {
                scratch_species_ids[right_offset] = @intCast(index);
                right_offset += 1;
            },
        };

        @memset(scratch_used[0..occurrence_count], false);
        const boson_ids = scratch_species_ids[0..boson_count];
        const left_ids = scratch_species_ids[boson_count .. boson_count + left_count];
        const right_ids = scratch_species_ids[boson_count + left_count .. boson_count + left_count + right_count];
        const boson_used = scratch_used[0..boson_count];
        const left_used = scratch_used[boson_count .. boson_count + left_count];
        const right_used = scratch_used[boson_count + left_count .. boson_count + left_count + right_count];

        var pair_count: usize = 0;
        var derivative_pair_weight: u16 = 0;

        const EmitCtx = struct {
            sink_ptr: @TypeOf(sink),
            candidate_row: plan.DiagramCandidateRow,
            summary_ptr: *PairingSummary,
            pairs_ptr: []PairingEntry,
            kernel_factors_ptr: []PairKernelFactor,
            boson_pair_count: u16,
            left_fermion_pair_count: u16,
            right_fermion_pair_count: u16,
        };

        const RightCtx = struct {
            emit_ctx: *EmitCtx,
            occurrences: []const PairingOccurrence,
            right_ids: []const u16,
            right_used: []bool,
        };

        const LeftCtx = struct {
            right_ctx: *RightCtx,
            occurrences: []const PairingOccurrence,
            left_ids: []const u16,
            left_used: []bool,
        };

        const BosonCtx = struct {
            left_ctx: *LeftCtx,
            occurrences: []const PairingOccurrence,
            boson_ids: []const u16,
            boson_used: []bool,
        };

        const emit_fn = struct {
            fn call(ctx: *EmitCtx, pair_count_ptr: *usize, derivative_weight_ptr: *u16) !void {
                try ctx.sink_ptr.emit(.{
                    .worldsheet = ctx.candidate_row.worldsheet,
                    .loop_order = ctx.candidate_row.loop_order,
                    .background = ctx.candidate_row.background,
                    .automorphism_denominator = ctx.candidate_row.automorphism_denominator,
                    .boson_pair_count = ctx.boson_pair_count,
                    .left_fermion_pair_count = ctx.left_fermion_pair_count,
                    .right_fermion_pair_count = ctx.right_fermion_pair_count,
                    .derivative_pair_weight = derivative_weight_ptr.*,
                    .vertices = ctx.candidate_row.vertices,
                    .pairs = ctx.pairs_ptr[0..pair_count_ptr.*],
                    .kernel_factors = ctx.kernel_factors_ptr[0..pair_count_ptr.*],
                });
                ctx.summary_ptr.emitted_count += 1;
            }
        };

        const right_fn = struct {
            fn call(ctx: *RightCtx, pair_count_ptr: *usize, derivative_weight_ptr: *u16) !void {
                if (ctx.right_ids.len == 0) return emit_fn.call(ctx.emit_ctx, pair_count_ptr, derivative_weight_ptr);
                return enumerateSpeciesPairings(
                    ctx.occurrences,
                    ctx.right_ids,
                    ctx.right_used,
                    .right_fermion,
                    ctx.emit_ctx.pairs_ptr,
                    ctx.emit_ctx.kernel_factors_ptr,
                    pair_count_ptr,
                    derivative_weight_ptr,
                    EmitCtx,
                    emit_fn.call,
                    ctx.emit_ctx,
                );
            }
        };

        const left_fn = struct {
            fn call(ctx: *LeftCtx, pair_count_ptr: *usize, derivative_weight_ptr: *u16) !void {
                if (ctx.left_ids.len == 0) return right_fn.call(ctx.right_ctx, pair_count_ptr, derivative_weight_ptr);
                return enumerateSpeciesPairings(
                    ctx.occurrences,
                    ctx.left_ids,
                    ctx.left_used,
                    .left_fermion,
                    ctx.right_ctx.emit_ctx.pairs_ptr,
                    ctx.right_ctx.emit_ctx.kernel_factors_ptr,
                    pair_count_ptr,
                    derivative_weight_ptr,
                    RightCtx,
                    right_fn.call,
                    ctx.right_ctx,
                );
            }
        };

        const boson_fn = struct {
            fn call(ctx: *BosonCtx, pair_count_ptr: *usize, derivative_weight_ptr: *u16) !void {
                if (ctx.boson_ids.len == 0) return left_fn.call(ctx.left_ctx, pair_count_ptr, derivative_weight_ptr);
                return enumerateSpeciesPairings(
                    ctx.occurrences,
                    ctx.boson_ids,
                    ctx.boson_used,
                    .boson,
                    ctx.left_ctx.right_ctx.emit_ctx.pairs_ptr,
                    ctx.left_ctx.right_ctx.emit_ctx.kernel_factors_ptr,
                    pair_count_ptr,
                    derivative_weight_ptr,
                    LeftCtx,
                    left_fn.call,
                    ctx.left_ctx,
                );
            }
        };

        var emit_ctx = EmitCtx{
            .sink_ptr = sink,
            .candidate_row = candidate,
            .summary_ptr = &summary,
            .pairs_ptr = scratch_pairs[0 .. occurrence_count / 2],
            .kernel_factors_ptr = scratch_kernel_factors[0 .. occurrence_count / 2],
            .boson_pair_count = @intCast(boson_count / 2),
            .left_fermion_pair_count = @intCast(left_count / 2),
            .right_fermion_pair_count = @intCast(right_count / 2),
        };
        var right_ctx = RightCtx{
            .emit_ctx = &emit_ctx,
            .occurrences = scratch_occurrences[0..occurrence_count],
            .right_ids = right_ids,
            .right_used = right_used,
        };
        var left_ctx = LeftCtx{
            .right_ctx = &right_ctx,
            .occurrences = scratch_occurrences[0..occurrence_count],
            .left_ids = left_ids,
            .left_used = left_used,
        };
        var boson_ctx = BosonCtx{
            .left_ctx = &left_ctx,
            .occurrences = scratch_occurrences[0..occurrence_count],
            .boson_ids = boson_ids,
            .boson_used = boson_used,
        };

        try boson_fn.call(&boson_ctx, &pair_count, &derivative_pair_weight);
    }

    return summary;
}

test "pairing engine keeps the one-loop bosonic metric candidate pairable" {
    const testing = std.testing;
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

    const BranchSink = struct {
        rows: []PairingBranchRow,
        pair_storage: []PairingEntry,
        kernel_storage: []PairKernelFactor,
        count: usize = 0,
        pair_offset: usize = 0,
        kernel_offset: usize = 0,
        pub fn emit(self: *@This(), row: PairingBranchRow) !void {
            const pair_start = self.pair_offset;
            const pair_end = pair_start + row.pairs.len;
            const kernel_start = self.kernel_offset;
            const kernel_end = kernel_start + row.kernel_factors.len;
            std.mem.copyForwards(PairingEntry, self.pair_storage[pair_start..pair_end], row.pairs);
            std.mem.copyForwards(PairKernelFactor, self.kernel_storage[kernel_start..kernel_end], row.kernel_factors);
            self.rows[self.count] = row;
            self.rows[self.count].pairs = self.pair_storage[pair_start..pair_end];
            self.rows[self.count].kernel_factors = self.kernel_storage[kernel_start..kernel_end];
            self.count += 1;
            self.pair_offset = pair_end;
            self.kernel_offset = kernel_end;
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

    var branch_storage: [2]PairingBranchRow = undefined;
    var pair_storage: [2]PairingEntry = undefined;
    var kernel_storage: [2]PairKernelFactor = undefined;
    var branch_sink = BranchSink{ .rows = &branch_storage, .pair_storage = &pair_storage, .kernel_storage = &kernel_storage };
    var occurrences: [8]PairingOccurrence = undefined;
    var species_ids: [8]u16 = undefined;
    var pairs: [4]PairingEntry = undefined;
    var kernel_factors: [4]PairKernelFactor = undefined;
    var used: [8]bool = undefined;
    const summary = try streamPairingBranches(catalog, candidate_storage[0..candidate_sink.count], &branch_sink, &occurrences, &species_ids, &pairs, &kernel_factors, &used);
    try testing.expectEqual(@as(usize, 1), summary.emitted_count);
    try testing.expectEqual(@as(u16, 1), branch_storage[0].boson_pair_count);
    try testing.expectEqual(@as(usize, 1), branch_storage[0].pairs.len);
    try testing.expectEqual(@as(usize, 1), branch_storage[0].kernel_factors.len);
    try testing.expectEqual(PairKernelKind.xi_xi, branch_storage[0].kernel_factors[0].kind);
}

test "pairing engine rejects odd fermion content" {
    const testing = std.testing;
    const candidate_vertices = [_]plan.VertexMultiplicity{
        .{ .vertex_index = 0, .multiplicity = 1 },
    };
    const candidate = [_]plan.DiagramCandidateRow{.{
        .worldsheet = .n1_1,
        .vertex_count = 1,
        .distinct_vertex_count = 1,
        .internal_propagator_count = 1,
        .loop_order = 1,
        .total_quantum_field_count = 1,
        .total_fermion_field_count = 1,
        .background = .{},
        .automorphism_denominator = 1,
        .vertices = &candidate_vertices,
    }};

    const fields = [_]rnc.VertexField{
        .{ .kind = .psi_left },
    };
    const catalog = [_]rnc.RncVertexRow{.{
        .worldsheet = .n1_1,
        .xi_order = 0,
        .fields = &fields,
    }};

    const Sink = struct {
        count: usize = 0,
        pub fn emit(self: *@This(), row: PairingBranchRow) !void {
            _ = row;
            self.count += 1;
        }
    };

    var sink = Sink{};
    var occurrences: [4]PairingOccurrence = undefined;
    var species_ids: [4]u16 = undefined;
    var pairs: [2]PairingEntry = undefined;
    var kernel_factors: [2]PairKernelFactor = undefined;
    var used: [4]bool = undefined;
    const summary = try streamPairingBranches(&catalog, &candidate, &sink, &occurrences, &species_ids, &pairs, &kernel_factors, &used);
    try testing.expectEqual(@as(usize, 0), summary.emitted_count);
    try testing.expectEqual(@as(u32, 1), summary.rejected_unpaired_count);
}

test "pairing engine drops mixed d-xi dbar-xi primitive pairs absent from cft-code" {
    const testing = std.testing;
    const candidate_vertices = [_]plan.VertexMultiplicity{
        .{ .vertex_index = 0, .multiplicity = 1 },
    };
    const candidate = [_]plan.DiagramCandidateRow{.{
        .worldsheet = .bosonic,
        .vertex_count = 1,
        .distinct_vertex_count = 1,
        .internal_propagator_count = 1,
        .loop_order = 1,
        .total_quantum_field_count = 2,
        .total_fermion_field_count = 0,
        .background = .{},
        .automorphism_denominator = 1,
        .vertices = &candidate_vertices,
    }};

    const fields = [_]rnc.VertexField{
        .{ .kind = .xi, .derivatives = .{ .holomorphic = 1 } },
        .{ .kind = .xi, .derivatives = .{ .antiholomorphic = 1 } },
    };
    const catalog = [_]rnc.RncVertexRow{.{
        .worldsheet = .bosonic,
        .xi_order = 2,
        .fields = &fields,
    }};

    const Sink = struct {
        count: usize = 0,
        pub fn emit(self: *@This(), row: PairingBranchRow) !void {
            _ = row;
            self.count += 1;
        }
    };

    var sink = Sink{};
    var occurrences: [4]PairingOccurrence = undefined;
    var species_ids: [4]u16 = undefined;
    var pairs: [2]PairingEntry = undefined;
    var kernel_factors: [2]PairKernelFactor = undefined;
    var used: [4]bool = undefined;
    const summary = try streamPairingBranches(&catalog, &candidate, &sink, &occurrences, &species_ids, &pairs, &kernel_factors, &used);
    try testing.expectEqual(@as(usize, 0), summary.emitted_count);
}

test "pairing engine classifies differentiated chiral fermion pairs from cft-code profiles" {
    const testing = std.testing;
    const candidate_vertices = [_]plan.VertexMultiplicity{
        .{ .vertex_index = 0, .multiplicity = 1 },
    };
    const candidate = [_]plan.DiagramCandidateRow{.{
        .worldsheet = .n1_1,
        .vertex_count = 1,
        .distinct_vertex_count = 1,
        .internal_propagator_count = 1,
        .loop_order = 1,
        .total_quantum_field_count = 2,
        .total_fermion_field_count = 2,
        .background = .{},
        .automorphism_denominator = 1,
        .vertices = &candidate_vertices,
    }};

    const fields = [_]rnc.VertexField{
        .{ .kind = .psi_left, .derivatives = .{ .holomorphic = 1 } },
        .{ .kind = .psi_left },
    };
    const catalog = [_]rnc.RncVertexRow{.{
        .worldsheet = .n1_1,
        .xi_order = 0,
        .fields = &fields,
    }};

    const Sink = struct {
        row: ?PairingBranchRow = null,

        pub fn emit(self: *@This(), row: PairingBranchRow) !void {
            self.row = row;
        }
    };

    var sink = Sink{};
    var occurrences: [4]PairingOccurrence = undefined;
    var species_ids: [4]u16 = undefined;
    var pairs: [2]PairingEntry = undefined;
    var kernel_factors: [2]PairKernelFactor = undefined;
    var used: [4]bool = undefined;
    const summary = try streamPairingBranches(&catalog, &candidate, &sink, &occurrences, &species_ids, &pairs, &kernel_factors, &used);
    try testing.expectEqual(@as(usize, 1), summary.emitted_count);
    try testing.expect(sink.row != null);
    try testing.expectEqual(PairKernelKind.psi_left_psi_left, sink.row.?.kernel_factors[0].kind);
    try testing.expectEqual(@as(u8, 1), sink.row.?.kernel_factors[0].derivative_order);
    try testing.expectEqual(@as(u8, 2), sink.row.?.kernel_factors[0].numerator_rank);
}
