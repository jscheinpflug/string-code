const std = @import("std");
const plan = @import("diagram_plan.zig");
const rnc = @import("rnc_vertices.zig");

/// WickSignatureRow is one pairable candidate summary before explicit branch generation.
pub const WickSignatureRow = struct {
    worldsheet: rnc.WorldsheetModel,
    loop_order: u8,
    background: plan.BackgroundLegCount,
    boson_pair_count: u16 = 0,
    left_fermion_pair_count: u16 = 0,
    right_fermion_pair_count: u16 = 0,
    derivative_pair_weight: u16 = 0,
    automorphism_denominator: u32 = 1,
    vertices: []const plan.VertexMultiplicity = &.{},
};

/// WickSignatureSummary reports how many candidates survive the pairability checks.
pub const WickSignatureSummary = struct {
    emitted_count: usize = 0,
    rejected_unpaired_count: u32 = 0,
    rejected_auxiliary_count: u32 = 0,
};

fn accumulateField(
    field: rnc.VertexField,
    bosons: *u16,
    left_fermions: *u16,
    right_fermions: *u16,
    derivative_weight: *u16,
) !void {
    derivative_weight.* += field.derivatives.holomorphic;
    derivative_weight.* += field.derivatives.antiholomorphic;

    switch (field.kind) {
        .xi => bosons.* += 1,
        .psi_left => left_fermions.* += 1,
        .psi_right => right_fermions.* += 1,
        .auxiliary => return error.UnsupportedAuxiliaryField,
    }
}

/// streamWickSignatures emits the pairable species-count summary of each candidate multiset.
pub fn streamWickSignatures(
    catalog: []const rnc.RncVertexRow,
    candidates: []const plan.DiagramCandidateRow,
    sink: anytype,
) !WickSignatureSummary {
    var summary = WickSignatureSummary{};

    for (candidates) |candidate| {
        var bosons: u16 = 0;
        var left_fermions: u16 = 0;
        var right_fermions: u16 = 0;
        var derivative_weight: u16 = 0;
        var has_auxiliary = false;

        for (candidate.vertices) |entry| {
            const row = catalog[entry.vertex_index];
            var repeat_index: u8 = 0;
            while (repeat_index < entry.multiplicity) : (repeat_index += 1) {
                for (row.fields) |field| {
                    accumulateField(field, &bosons, &left_fermions, &right_fermions, &derivative_weight) catch {
                        has_auxiliary = true;
                        break;
                    };
                }
                if (has_auxiliary) break;
            }
            if (has_auxiliary) break;
        }

        if (has_auxiliary) {
            summary.rejected_auxiliary_count += 1;
            continue;
        }

        if (bosons % 2 != 0 or left_fermions % 2 != 0 or right_fermions % 2 != 0) {
            summary.rejected_unpaired_count += 1;
            continue;
        }

        try sink.emit(.{
            .worldsheet = candidate.worldsheet,
            .loop_order = candidate.loop_order,
            .background = candidate.background,
            .boson_pair_count = @divExact(bosons, 2),
            .left_fermion_pair_count = @divExact(left_fermions, 2),
            .right_fermion_pair_count = @divExact(right_fermions, 2),
            .derivative_pair_weight = @divExact(derivative_weight, 2),
            .automorphism_denominator = candidate.automorphism_denominator,
            .vertices = candidate.vertices,
        });
        summary.emitted_count += 1;
    }

    return summary;
}

test "wick signatures keep the one-loop bosonic metric candidate pairable" {
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

    const WickSink = struct {
        rows: []WickSignatureRow,
        count: usize = 0,
        pub fn emit(self: *@This(), row: WickSignatureRow) !void {
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

    var rows: [4]WickSignatureRow = undefined;
    var wick_sink = WickSink{ .rows = &rows };
    const summary = try streamWickSignatures(catalog, candidate_storage[0..candidate_sink.count], &wick_sink);
    try testing.expectEqual(@as(usize, 1), summary.emitted_count);
    try testing.expectEqual(@as(u16, 1), rows[0].boson_pair_count);
    try testing.expectEqual(@as(u16, 0), rows[0].derivative_pair_weight);
}

test "wick signatures reject odd fermion content" {
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
        pub fn emit(self: *@This(), row: WickSignatureRow) !void {
            _ = row;
            self.count += 1;
        }
    };

    var sink = Sink{};
    const summary = try streamWickSignatures(&catalog, &candidate, &sink);
    try testing.expectEqual(@as(usize, 0), summary.emitted_count);
    try testing.expectEqual(@as(u32, 1), summary.rejected_unpaired_count);
}
