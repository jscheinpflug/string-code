const std = @import("std");
const rnc = @import("rnc_vertices.zig");

/// BackgroundLegCount fixes the local operator signature required at the end of one branch.
pub const BackgroundLegCount = struct {
    d_x0: u8 = 0,
    dbar_x0: u8 = 0,
};

/// DiagramPlanRequest selects the candidate multiset families enumerated from one vertex catalog.
pub const DiagramPlanRequest = struct {
    worldsheet: rnc.WorldsheetModel,
    loop_order: u8,
    max_vertices: u8,
    required_background: BackgroundLegCount = .{},
    include_fermions: bool = true,
};

/// VertexMultiplicity records one catalog row and its multiplicity in a candidate multiset.
pub const VertexMultiplicity = struct {
    vertex_index: u16,
    multiplicity: u8,
};

/// DiagramCandidateRow is one compact candidate multiset before explicit Wick pairing.
pub const DiagramCandidateRow = struct {
    worldsheet: rnc.WorldsheetModel,
    vertex_count: u8,
    distinct_vertex_count: u8,
    internal_propagator_count: u16,
    loop_order: u8,
    total_quantum_field_count: u16,
    total_fermion_field_count: u16,
    background: BackgroundLegCount,
    automorphism_denominator: u32,
    vertices: []const VertexMultiplicity = &.{},
};

fn factorial(value: u8) u32 {
    var result: u32 = 1;
    var k: u8 = 2;
    while (k <= value) : (k += 1) result *= k;
    return result;
}

fn fieldCounts(row: rnc.RncVertexRow, include_fermions: bool) ?struct {
    quantum_fields: u16,
    fermion_fields: u16,
    background: BackgroundLegCount,
} {
    var quantum_fields: u16 = 0;
    var fermion_fields: u16 = 0;
    var background = BackgroundLegCount{};

    for (row.fields) |field| {
        switch (field.kind) {
            .xi => quantum_fields += 1,
            .psi_left, .psi_right => {
                if (!include_fermions) return null;
                quantum_fields += 1;
                fermion_fields += 1;
            },
            .auxiliary => return null,
        }
    }

    for (row.background_legs) |leg| switch (leg.kind) {
        .d_x0 => background.d_x0 += 1,
        .dbar_x0 => background.dbar_x0 += 1,
    };

    return .{
        .quantum_fields = quantum_fields,
        .fermion_fields = fermion_fields,
        .background = background,
    };
}

fn candidateMatches(request: DiagramPlanRequest, row: DiagramCandidateRow) bool {
    return row.worldsheet == request.worldsheet and
        row.loop_order == request.loop_order and
        row.background.d_x0 == request.required_background.d_x0 and
        row.background.dbar_x0 == request.required_background.dbar_x0 and
        (!request.include_fermions or row.total_fermion_field_count % 2 == 0);
}

fn emitCandidate(
    request: DiagramPlanRequest,
    catalog: []const rnc.RncVertexRow,
    multiplicities: []const u8,
    output_vertices: []VertexMultiplicity,
    sink: anytype,
) !void {
    var vertex_count: u8 = 0;
    var distinct_vertex_count: u8 = 0;
    var total_quantum_fields: u16 = 0;
    var total_fermion_fields: u16 = 0;
    var background = BackgroundLegCount{};
    var automorphism_denominator: u32 = 1;

    for (catalog, multiplicities, 0..) |row, multiplicity, index| {
        if (multiplicity == 0) continue;
        const counts = fieldCounts(row, request.include_fermions) orelse return;

        vertex_count += multiplicity;
        distinct_vertex_count += 1;
        total_quantum_fields += counts.quantum_fields * multiplicity;
        total_fermion_fields += counts.fermion_fields * multiplicity;
        background.d_x0 += counts.background.d_x0 * multiplicity;
        background.dbar_x0 += counts.background.dbar_x0 * multiplicity;
        automorphism_denominator *= factorial(multiplicity);

        output_vertices[distinct_vertex_count - 1] = .{
            .vertex_index = @intCast(index),
            .multiplicity = multiplicity,
        };
    }

    if (vertex_count == 0) return;
    if (total_quantum_fields % 2 != 0) return;

    const internal_propagator_count: u16 = @divExact(total_quantum_fields, 2);
    const loop_order_signed = @as(i32, internal_propagator_count) - vertex_count + 1;
    if (loop_order_signed < 0) return;

    const row = DiagramCandidateRow{
        .worldsheet = request.worldsheet,
        .vertex_count = vertex_count,
        .distinct_vertex_count = distinct_vertex_count,
        .internal_propagator_count = internal_propagator_count,
        .loop_order = @intCast(loop_order_signed),
        .total_quantum_field_count = total_quantum_fields,
        .total_fermion_field_count = total_fermion_fields,
        .background = background,
        .automorphism_denominator = automorphism_denominator,
        .vertices = output_vertices[0..distinct_vertex_count],
    };

    if (!candidateMatches(request, row)) return;
    try sink.emit(row);
}

fn enumerateRec(
    request: DiagramPlanRequest,
    catalog: []const rnc.RncVertexRow,
    multiplicities: []u8,
    next_index: usize,
    remaining_vertices: u8,
    output_vertices: []VertexMultiplicity,
    sink: anytype,
) !void {
    if (next_index == catalog.len) {
        if (remaining_vertices == 0) {
            try emitCandidate(request, catalog, multiplicities, output_vertices, sink);
        }
        return;
    }

    var multiplicity: u8 = 0;
    while (multiplicity <= remaining_vertices) : (multiplicity += 1) {
        multiplicities[next_index] = multiplicity;
        try enumerateRec(request, catalog, multiplicities, next_index + 1, remaining_vertices - multiplicity, output_vertices, sink);
    }
}

/// streamDiagramCandidates enumerates candidate vertex multisets for one requested loop order.
pub fn streamDiagramCandidates(request: DiagramPlanRequest, catalog: []const rnc.RncVertexRow, sink: anytype, scratch_multiplicities: []u8, scratch_vertices: []VertexMultiplicity) !void {
    if (scratch_multiplicities.len < catalog.len) return error.ScratchTooSmall;
    if (scratch_vertices.len < catalog.len) return error.ScratchTooSmall;

    @memset(scratch_multiplicities[0..catalog.len], 0);

    var vertex_total: u8 = 1;
    while (vertex_total <= request.max_vertices) : (vertex_total += 1) {
        try enumerateRec(
            request,
            catalog,
            scratch_multiplicities[0..catalog.len],
            0,
            vertex_total,
            scratch_vertices[0..catalog.len],
            sink,
        );
    }
}

test "diagram plan finds the bosonic one-loop metric candidate" {
    const testing = std.testing;
    const Sink = struct {
        rows: []DiagramCandidateRow,
        count: usize = 0,

        fn emit(self: *@This(), row: DiagramCandidateRow) !void {
            if (self.count == self.rows.len) return error.OutputTooSmall;
            self.rows[self.count] = row;
            self.count += 1;
        }
    };

    var catalog_storage: [4]rnc.RncVertexRow = undefined;
    const CatalogSink = struct {
        rows: []rnc.RncVertexRow,
        count: usize = 0,

        pub fn emit(self: *@This(), row: rnc.RncVertexRow) !void {
            self.rows[self.count] = row;
            self.count += 1;
        }
    };

    var catalog_sink = CatalogSink{ .rows = &catalog_storage };
    try rnc.streamBootstrapVertices(.{ .worldsheet = .bosonic, .max_xi_order = 2, .include_fermions = false }, &catalog_sink);
    const catalog = catalog_storage[0..catalog_sink.count];

    var rows: [4]DiagramCandidateRow = undefined;
    var sink = Sink{ .rows = &rows };
    var multiplicities: [4]u8 = undefined;
    var vertices: [4]VertexMultiplicity = undefined;
    try streamDiagramCandidates(.{
        .worldsheet = .bosonic,
        .loop_order = 1,
        .max_vertices = 1,
        .required_background = .{ .d_x0 = 1, .dbar_x0 = 1 },
        .include_fermions = false,
    }, catalog, &sink, &multiplicities, &vertices);

    try testing.expectEqual(@as(usize, 1), sink.count);
    try testing.expectEqual(@as(u8, 1), rows[0].vertex_count);
    try testing.expectEqual(@as(u16, 1), rows[0].internal_propagator_count);
    try testing.expectEqual(@as(u32, 1), rows[0].automorphism_denominator);
}

test "diagram plan excludes fermion rows when the request is bosonic" {
    const testing = std.testing;
    const Sink = struct {
        count: usize = 0,
        fn emit(self: *@This(), row: DiagramCandidateRow) !void {
            _ = row;
            self.count += 1;
        }
    };

    var catalog_storage: [8]rnc.RncVertexRow = undefined;
    const CatalogSink = struct {
        rows: []rnc.RncVertexRow,
        count: usize = 0,

        pub fn emit(self: *@This(), row: rnc.RncVertexRow) !void {
            self.rows[self.count] = row;
            self.count += 1;
        }
    };

    var catalog_sink = CatalogSink{ .rows = &catalog_storage };
    try rnc.streamBootstrapVertices(.{ .worldsheet = .n1_1, .max_xi_order = 2, .include_fermions = true }, &catalog_sink);
    const catalog = catalog_storage[0..catalog_sink.count];

    var sink = Sink{};
    var multiplicities: [8]u8 = undefined;
    var vertices: [8]VertexMultiplicity = undefined;
    try streamDiagramCandidates(.{
        .worldsheet = .n1_1,
        .loop_order = 2,
        .max_vertices = 1,
        .required_background = .{},
        .include_fermions = false,
    }, catalog, &sink, &multiplicities, &vertices);

    try testing.expectEqual(@as(usize, 0), sink.count);
}
