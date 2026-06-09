const std = @import("std");
const geometry = @import("local_geometry_reducer.zig");

/// SourceWorldsheet selects the component sigma-model field content carried by one source row.
pub const SourceWorldsheet = enum(u8) {
    bosonic,
    n1_1,
};

/// SourceFieldKind identifies one quantum field occurrence in a component source term.
pub const SourceFieldKind = enum(u8) {
    xi,
    psi_left,
    psi_right,
};

/// SourceBackgroundLegKind identifies one surviving background leg in a component source term.
pub const SourceBackgroundLegKind = enum(u8) {
    d_x0,
    dbar_x0,
};

/// SourceVertexTensorKind names one background tensor family in the component expansion.
pub const SourceVertexTensorKind = enum(u8) {
    metric,
    riemann,
    covariant_derivative_riemann,
};

/// SourceFamily names the first explicit component RNC families emitted by the source table.
pub const SourceFamily = enum(u8) {
    kinetic,
    riemann_mass,
    nabla_riemann_mass,
    nabla2_riemann_mass,
    riemann_square_mass,
    fermion_connection_riemann,
    fermion_connection_nabla_riemann,
    fermion_metric_derivative_riemann,
    fermion_riemann,
};

/// SourceLoweringChannel records whether a source row lowers to primitive Wick kernels or only to contact terms.
pub const SourceLoweringChannel = enum(u8) {
    primitive,
    contact_only,
};

/// SourceDerivatives stores the worldsheet derivative content of one source field.
pub const SourceDerivatives = packed struct(u8) {
    holomorphic: u4 = 0,
    antiholomorphic: u4 = 0,
};

/// SourceField is one quantum field occurrence in a source row.
pub const SourceField = struct {
    kind: SourceFieldKind,
    target_sort: geometry.TensorSlotSort = .real_tangent,
    derivatives: SourceDerivatives = .{},
};

/// SourceBackgroundLeg is one uncontracted local background leg.
pub const SourceBackgroundLeg = struct {
    kind: SourceBackgroundLegKind,
    target_sort: geometry.TensorSlotSort = .real_tangent,
};

/// SourceTensor is one target-space tensor occurrence in a source row.
pub const SourceTensor = struct {
    kind: SourceVertexTensorKind,
    slot_sorts: []const geometry.TensorSlotSort = &.{},
    covariant_derivative_count: u8 = 0,
};

/// ComponentSourceRow is one explicit component-level RNC source term before lowering.
pub const ComponentSourceRow = struct {
    family: SourceFamily,
    worldsheet: SourceWorldsheet,
    channel: SourceLoweringChannel = .primitive,
    xi_order: u8,
    fields: []const SourceField = &.{},
    background_legs: []const SourceBackgroundLeg = &.{},
    tensors: []const SourceTensor = &.{},
    coefficient: i16 = 1,
    symmetry_denominator: u16 = 1,
    alpha_prime_power: i16 = 0,
};

pub const SourceRequest = struct {
    worldsheet: SourceWorldsheet,
    max_xi_order: u8,
    include_fermions: bool = true,
    include_higher_metric_terms: bool = true,
    include_contact_only: bool = false,
};

const d = SourceDerivatives;
const real = geometry.TensorSlotSort.real_tangent;

const bosonic_kinetic_fields = [_]SourceField{
    .{ .kind = .xi, .target_sort = real, .derivatives = d{ .holomorphic = 1 } },
    .{ .kind = .xi, .target_sort = real, .derivatives = d{ .antiholomorphic = 1 } },
};

const bosonic_curvature_fields = [_]SourceField{
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .xi, .target_sort = real },
};

const bosonic_nabla_curvature_fields = [_]SourceField{
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .xi, .target_sort = real },
};

const bosonic_nabla2_curvature_fields = [_]SourceField{
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .xi, .target_sort = real },
};

const bosonic_background_legs = [_]SourceBackgroundLeg{
    .{ .kind = .d_x0, .target_sort = real },
    .{ .kind = .dbar_x0, .target_sort = real },
};

const metric_tensor_sorts = [_]geometry.TensorSlotSort{ real, real };
const riemann_tensor_sorts = [_]geometry.TensorSlotSort{ real, real, real, real };

const bosonic_kinetic_tensors = [_]SourceTensor{
    .{ .kind = .metric, .slot_sorts = &metric_tensor_sorts },
};

const bosonic_curvature_tensors = [_]SourceTensor{
    .{ .kind = .riemann, .slot_sorts = &riemann_tensor_sorts },
};

const bosonic_nabla_curvature_tensors = [_]SourceTensor{
    .{ .kind = .covariant_derivative_riemann, .slot_sorts = &riemann_tensor_sorts, .covariant_derivative_count = 1 },
};

const bosonic_nabla2_curvature_tensors = [_]SourceTensor{
    .{ .kind = .covariant_derivative_riemann, .slot_sorts = &riemann_tensor_sorts, .covariant_derivative_count = 2 },
};

const bosonic_riemann_square_tensors = [_]SourceTensor{
    .{ .kind = .riemann, .slot_sorts = &riemann_tensor_sorts },
    .{ .kind = .riemann, .slot_sorts = &riemann_tensor_sorts },
};

const fermion_curvature_fields = [_]SourceField{
    .{ .kind = .psi_left, .target_sort = real },
    .{ .kind = .psi_left, .target_sort = real },
    .{ .kind = .psi_right, .target_sort = real },
    .{ .kind = .psi_right, .target_sort = real },
};

const left_fermion_connection_fields = [_]SourceField{
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .psi_left, .target_sort = real },
    .{ .kind = .psi_left, .target_sort = real },
};

const right_fermion_connection_fields = [_]SourceField{
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .psi_right, .target_sort = real },
    .{ .kind = .psi_right, .target_sort = real },
};

const left_fermion_nabla_connection_fields = [_]SourceField{
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .psi_left, .target_sort = real },
    .{ .kind = .psi_left, .target_sort = real },
};

const right_fermion_nabla_connection_fields = [_]SourceField{
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .psi_right, .target_sort = real },
    .{ .kind = .psi_right, .target_sort = real },
};

const left_fermion_metric_derivative_fields = [_]SourceField{
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .psi_left, .target_sort = real },
    .{ .kind = .psi_left, .target_sort = real, .derivatives = d{ .antiholomorphic = 1 } },
};

const right_fermion_metric_derivative_fields = [_]SourceField{
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .xi, .target_sort = real },
    .{ .kind = .psi_right, .target_sort = real },
    .{ .kind = .psi_right, .target_sort = real, .derivatives = d{ .holomorphic = 1 } },
};

const left_fermion_background_leg = [_]SourceBackgroundLeg{
    .{ .kind = .dbar_x0, .target_sort = real },
};

const right_fermion_background_leg = [_]SourceBackgroundLeg{
    .{ .kind = .d_x0, .target_sort = real },
};

const fermion_curvature_tensors = [_]SourceTensor{
    .{ .kind = .riemann, .slot_sorts = &riemann_tensor_sorts },
};

const source_rows = [_]ComponentSourceRow{
    .{ .family = .kinetic, .worldsheet = .bosonic, .xi_order = 2, .fields = &bosonic_kinetic_fields, .tensors = &bosonic_kinetic_tensors },
    .{ .family = .riemann_mass, .worldsheet = .bosonic, .xi_order = 2, .fields = &bosonic_curvature_fields, .background_legs = &bosonic_background_legs, .tensors = &bosonic_curvature_tensors, .symmetry_denominator = 3 },
    .{ .family = .nabla_riemann_mass, .worldsheet = .bosonic, .xi_order = 3, .fields = &bosonic_nabla_curvature_fields, .background_legs = &bosonic_background_legs, .tensors = &bosonic_nabla_curvature_tensors, .symmetry_denominator = 6 },
    .{ .family = .nabla2_riemann_mass, .worldsheet = .bosonic, .xi_order = 4, .fields = &bosonic_nabla2_curvature_fields, .background_legs = &bosonic_background_legs, .tensors = &bosonic_nabla2_curvature_tensors, .symmetry_denominator = 20 },
    .{ .family = .riemann_square_mass, .worldsheet = .bosonic, .xi_order = 4, .fields = &bosonic_nabla2_curvature_fields, .background_legs = &bosonic_background_legs, .tensors = &bosonic_riemann_square_tensors, .coefficient = 2, .symmetry_denominator = 45 },
    .{ .family = .kinetic, .worldsheet = .n1_1, .xi_order = 2, .fields = &bosonic_kinetic_fields, .tensors = &bosonic_kinetic_tensors },
    .{ .family = .riemann_mass, .worldsheet = .n1_1, .xi_order = 2, .fields = &bosonic_curvature_fields, .background_legs = &bosonic_background_legs, .tensors = &bosonic_curvature_tensors, .symmetry_denominator = 3 },
    .{ .family = .nabla_riemann_mass, .worldsheet = .n1_1, .xi_order = 3, .fields = &bosonic_nabla_curvature_fields, .background_legs = &bosonic_background_legs, .tensors = &bosonic_nabla_curvature_tensors, .symmetry_denominator = 6 },
    .{ .family = .nabla2_riemann_mass, .worldsheet = .n1_1, .xi_order = 4, .fields = &bosonic_nabla2_curvature_fields, .background_legs = &bosonic_background_legs, .tensors = &bosonic_nabla2_curvature_tensors, .symmetry_denominator = 20 },
    .{ .family = .riemann_square_mass, .worldsheet = .n1_1, .xi_order = 4, .fields = &bosonic_nabla2_curvature_fields, .background_legs = &bosonic_background_legs, .tensors = &bosonic_riemann_square_tensors, .coefficient = 2, .symmetry_denominator = 45 },
    .{ .family = .fermion_connection_riemann, .worldsheet = .n1_1, .xi_order = 1, .fields = &left_fermion_connection_fields, .background_legs = &left_fermion_background_leg, .tensors = &bosonic_curvature_tensors, .coefficient = -1, .symmetry_denominator = 3 },
    .{ .family = .fermion_connection_riemann, .worldsheet = .n1_1, .xi_order = 1, .fields = &right_fermion_connection_fields, .background_legs = &right_fermion_background_leg, .tensors = &bosonic_curvature_tensors, .coefficient = -1, .symmetry_denominator = 3 },
    .{ .family = .fermion_connection_nabla_riemann, .worldsheet = .n1_1, .xi_order = 2, .fields = &left_fermion_nabla_connection_fields, .background_legs = &left_fermion_background_leg, .tensors = &bosonic_nabla_curvature_tensors, .coefficient = -1, .symmetry_denominator = 6 },
    .{ .family = .fermion_connection_nabla_riemann, .worldsheet = .n1_1, .xi_order = 2, .fields = &right_fermion_nabla_connection_fields, .background_legs = &right_fermion_background_leg, .tensors = &bosonic_nabla_curvature_tensors, .coefficient = -1, .symmetry_denominator = 6 },
    .{ .family = .fermion_metric_derivative_riemann, .worldsheet = .n1_1, .channel = .contact_only, .xi_order = 2, .fields = &left_fermion_metric_derivative_fields, .tensors = &bosonic_curvature_tensors, .symmetry_denominator = 3 },
    .{ .family = .fermion_metric_derivative_riemann, .worldsheet = .n1_1, .channel = .contact_only, .xi_order = 2, .fields = &right_fermion_metric_derivative_fields, .tensors = &bosonic_curvature_tensors, .symmetry_denominator = 3 },
    .{ .family = .fermion_riemann, .worldsheet = .n1_1, .xi_order = 0, .fields = &fermion_curvature_fields, .tensors = &fermion_curvature_tensors },
};

fn fieldMatchesCurrentLowering(field: SourceField) bool {
    return switch (field.kind) {
        .xi => true,
        .psi_left => field.derivatives.antiholomorphic == 0,
        .psi_right => field.derivatives.holomorphic == 0,
    };
}

fn rowMatchesCurrentLowering(row: ComponentSourceRow) bool {
    for (row.fields) |field| {
        if (!fieldMatchesCurrentLowering(field)) return false;
    }
    return true;
}

fn matchesRequest(row: ComponentSourceRow, request: SourceRequest) bool {
    if (row.worldsheet != request.worldsheet) return false;
    if (row.channel == .contact_only and !request.include_contact_only) return false;
    if (row.xi_order > request.max_xi_order) return false;
    if (!request.include_higher_metric_terms) switch (row.family) {
        .kinetic, .riemann_mass, .fermion_connection_riemann, .fermion_metric_derivative_riemann, .fermion_riemann => {},
        .nabla_riemann_mass, .nabla2_riemann_mass, .riemann_square_mass, .fermion_connection_nabla_riemann => return false,
    };
    if (request.include_fermions) return true;
    for (row.fields) |field| switch (field.kind) {
        .psi_left, .psi_right => return false,
        .xi => {},
    };
    return true;
}

/// streamSources emits the first explicit component RNC source families.
pub fn streamSources(request: SourceRequest, sink: anytype) !void {
    for (source_rows) |row| {
        if (!matchesRequest(row, request)) continue;
        if (row.channel == .primitive and !rowMatchesCurrentLowering(row)) {
            return error.UnsupportedFermionDerivativeLowering;
        }
        try sink.emit(row);
    }
}

test "contact-only differentiated fermion metric rows are opt-in" {
    const testing = std.testing;
    const Sink = struct {
        rows: []ComponentSourceRow,
        count: usize = 0,

        fn emit(self: *@This(), row: ComponentSourceRow) !void {
            if (self.count == self.rows.len) return error.OutputTooSmall;
            self.rows[self.count] = row;
            self.count += 1;
        }
    };

    var primitive_rows: [16]ComponentSourceRow = undefined;
    var primitive_sink = Sink{ .rows = &primitive_rows };
    try streamSources(.{
        .worldsheet = .n1_1,
        .max_xi_order = 2,
        .include_fermions = true,
        .include_higher_metric_terms = true,
    }, &primitive_sink);
    try testing.expectEqual(@as(usize, 6), primitive_sink.count);
    for (primitive_rows[0..primitive_sink.count]) |row| {
        try testing.expectEqual(SourceLoweringChannel.primitive, row.channel);
    }

    var all_rows: [16]ComponentSourceRow = undefined;
    var all_sink = Sink{ .rows = &all_rows };
    try streamSources(.{
        .worldsheet = .n1_1,
        .max_xi_order = 2,
        .include_fermions = true,
        .include_higher_metric_terms = true,
        .include_contact_only = true,
    }, &all_sink);
    try testing.expectEqual(@as(usize, 8), all_sink.count);

    var found_left_raw = false;
    var found_right_raw = false;
    for (all_rows[0..all_sink.count]) |row| {
        if (row.family != .fermion_metric_derivative_riemann) continue;
        try testing.expectEqual(SourceLoweringChannel.contact_only, row.channel);
        if (row.fields.len != 4) continue;
        if (row.fields[2].kind == .psi_left and row.fields[3].kind == .psi_left and row.fields[3].derivatives.antiholomorphic == 1) {
            found_left_raw = true;
        }
        if (row.fields[2].kind == .psi_right and row.fields[3].kind == .psi_right and row.fields[3].derivatives.holomorphic == 1) {
            found_right_raw = true;
        }
    }
    try testing.expect(found_left_raw);
    try testing.expect(found_right_raw);
}
