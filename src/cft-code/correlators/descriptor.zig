const std = @import("std");
const kernel = @import("../kernel.zig");
const normal_ordering = @import("../normal-ordering/normal-ordering.zig");
const operators = @import("../expressions/operators.zig");
const shared = @import("../presets/shared.zig");

const declare = shared.declare;
const wick = declare.wick;
const zero_mode = declare.zero_mode;
const scalars = declare.scalars;

/// descriptor_abi_version is the generated descriptor table ABI understood here.
pub const descriptor_abi_version: u32 = 2;

/// Id is one dense descriptor table index.
pub const Id = u16;

/// LabelRole classifies a generated field label.
pub const LabelRole = enum {
    vector_index,
    momentum,
    profile,
    scalar_parameter,
    modular_parameter,
};

/// SurfaceKind names the supported topology class.
pub const SurfaceKind = enum {
    sphere,
    torus,
};

/// CoordinateModel selects rational or elliptic coordinate kernels.
pub const CoordinateModel = enum {
    rational,
    elliptic,
};

/// Statistics records the exchange parity of one field family.
pub const Statistics = enum {
    bosonic,
    fermionic,
};

/// InsertionShape gives the coordinate slots carried by a field insertion.
pub const InsertionShape = enum {
    single,
    pair,
};

/// Parameter declares one generated scalar or modular parameter.
pub const Parameter = struct {
    id: Id,
    symbol: Id,
    role: LabelRole,
};

/// QuantumNumberKind classifies a conserved or representation-valued label.
pub const QuantumNumberKind = enum {
    u1_charge,
    ade_irrep,
};

/// QuantumNumber declares one basis-selection quantum number.
pub const QuantumNumber = struct {
    id: Id,
    symbol: Id,
    kind: QuantumNumberKind,
    group_symbol: ?Id = null,
};

/// QuantumNumberValue stores one compact field quantum-number value.
pub const QuantumNumberValue = union(enum) {
    integer: i64,
    rational: Rational,
    symbol: Id,
};

/// FieldQuantumNumber assigns one quantum-number value to one field family.
pub const FieldQuantumNumber = struct {
    field: Id,
    quantum_number: Id,
    value: QuantumNumberValue,
};

/// Surface declares one coordinate model for a generated rule set.
pub const Surface = struct {
    id: Id,
    kind: SurfaceKind,
    coordinate_model: CoordinateModel,
    modular_parameter: ?Id = null,
};

/// LabelSchema declares one field label slot.
pub const LabelSchema = struct {
    id: Id,
    role: LabelRole,
    symbol: Id,
};

/// Field declares one generated local field family.
pub const Field = struct {
    id: Id,
    symbol: Id,
    insertion: InsertionShape,
    labels: []const LabelSchema = &.{},
    statistics: Statistics,
    zero_mode_consumable: bool = false,
    weight: ?Id = null,
    anti_weight: ?Id = null,
};

/// Rational is one exact small rational value.
pub const Rational = struct {
    numerator: i64,
    denominator: i64,
};

/// MetadataExpr is a compact expression tree over ids, labels, and parameters.
pub const MetadataExpr = union(enum) {
    rational: Rational,
    parameter: Id,
    field_label: struct { field: Id, label: Id },
    add: struct { left: Id, right: Id },
    mul: struct { left: Id, right: Id },
    bilinear: struct { left: Id, right: Id, form_symbol: Id },
};

/// Side selects the left or right endpoint of a Wick rule.
pub const Side = enum {
    left,
    right,
};

/// CoordinateSlot selects one coordinate component from an insertion.
pub const CoordinateSlot = enum {
    position,
    holomorphic,
    antiholomorphic,
};

/// CoordinateRef names one coordinate slot on one endpoint.
pub const CoordinateRef = struct {
    side: Side,
    slot: CoordinateSlot,
};

/// LabelRef names one label slot on one endpoint.
pub const LabelRef = struct {
    side: Side,
    slot: Id,
};

/// PairIndexConstraint selects one local index-sort compatibility check.
pub const PairIndexConstraint = enum(u8) {
    none,
    same_sort,
    conjugate_complex_sort,
};

/// PairIndexConstraintRow checks one label slot on each Wick endpoint.
pub const PairIndexConstraintRow = struct {
    left_slot: Id,
    right_slot: Id,
    constraint: PairIndexConstraint,
};

/// ScalarFactor describes one scalar multiplier in a Wick term.
pub const ScalarFactor = union(enum) {
    one,
    rational: Rational,
    parameter: Id,
    neg_parameter_half: Id,
    neg_i_parameter_half: Id,
    parameter_half: Id,
};

/// CoordinateFactor describes one coordinate multiplier in a Wick term.
pub const CoordinateFactor = union(enum) {
    difference_power: struct { left: CoordinateRef, right: CoordinateRef, exponent: i16, derive_left: bool = false, derive_right: bool = false },
    logarithm: struct { left: CoordinateRef, right: CoordinateRef, derive_left: bool = false, derive_right: bool = false },
    named_kernel: struct { symbol: Id, left: CoordinateRef, right: CoordinateRef, derive_left: bool = false, derive_right: bool = false },
    green_exponential: struct { left: CoordinateRef, right: CoordinateRef },
};

/// TensorFactor describes one tensor multiplier in a Wick term.
pub const TensorFactor = union(enum) {
    none,
    metric: struct { left: LabelRef, right: LabelRef },
    momentum_index: struct { momentum: LabelRef, index: LabelRef },
    momentum_pair: struct { left: LabelRef, right: LabelRef },
};

/// ActionFactor describes an operation applied to a residual factor.
pub const ActionFactor = union(enum) {
    profile_derivative: struct { profile: LabelRef, index: LabelRef },
};

/// WickTerm is one product in a primitive Wick-rule sum.
pub const WickTerm = struct {
    scalars: []const ScalarFactor = &.{},
    coordinates: []const CoordinateFactor = &.{},
    tensors: []const TensorFactor = &.{},
    actions: []const ActionFactor = &.{},
    residuals: []const Side = &.{},
};

/// WickRule declares primitive pair terms for two field families.
pub const WickRule = struct {
    surface: Id,
    left: Id,
    right: Id,
    terms: []const WickTerm,
    index_constraints: []const PairIndexConstraintRow = &.{},
};

/// ZeroModeKind selects one implemented residual base-case primitive.
pub const ZeroModeKind = enum {
    constant_fermion,
    top_form_fermion,
    boson_momentum_conservation,
};

/// ZeroModeRule declares one residual base-case primitive.
pub const ZeroModeRule = struct {
    surface: Id,
    kind: ZeroModeKind,
    consumes: []const Id,
    normalization: ScalarFactor = .one,
    two_pi_power: u16 = 0,
};

/// ReservedServices records descriptor slots not implemented in this slice.
pub const ReservedServices = struct {
    ope_rules: usize = 0,
    operator_templates: usize = 0,
    relation_rules: usize = 0,
    basis_rules: usize = 0,
};

/// Descriptor is the generated theory data consumed by the lowerer.
pub const Descriptor = struct {
    abi_version: u32 = descriptor_abi_version,
    theory_symbol: Id,
    theory_hash: u32,
    symbols: []const []const u8,
    parameters: []const Parameter = &.{},
    quantum_numbers: []const QuantumNumber = &.{},
    field_quantum_numbers: []const FieldQuantumNumber = &.{},
    surfaces: []const Surface,
    fields: []const Field,
    metadata: []const MetadataExpr = &.{},
    wick_rules: []const WickRule,
    zero_modes: []const ZeroModeRule = &.{},
    result_symbols: []const Id = &.{},
    reserved: ReservedServices = .{},
};

fn denseUniqueIds(comptime T: type, items: []const T) !void {
    var seen: [256]bool = [_]bool{false} ** 256;
    for (items) |item| {
        if (item.id >= items.len) return error.NonDenseId;
        if (seen[item.id]) return error.DuplicateId;
        seen[item.id] = true;
    }
}

fn hasSymbol(d: Descriptor, symbol: Id) bool {
    return symbol < d.symbols.len;
}

fn hasParameter(d: Descriptor, id: Id) bool {
    return id < d.parameters.len and d.parameters[id].id == id;
}

fn hasQuantumNumber(d: Descriptor, id: Id) bool {
    return id < d.quantum_numbers.len and d.quantum_numbers[id].id == id;
}

fn hasSurface(d: Descriptor, id: Id) bool {
    return id < d.surfaces.len and d.surfaces[id].id == id;
}

fn hasField(d: Descriptor, id: Id) bool {
    return id < d.fields.len and d.fields[id].id == id;
}

fn fieldLabel(field: Field, id: Id) ?LabelSchema {
    for (field.labels) |label| {
        if (label.id == id) return label;
    }
    return null;
}

fn validateLabelRef(d: Descriptor, field_id: Id, label_id: Id) !void {
    if (!hasField(d, field_id)) return error.DanglingField;
    if (fieldLabel(d.fields[field_id], label_id) == null) return error.DanglingLabel;
}

fn validateMetadata(d: Descriptor, index: Id, expr: MetadataExpr) !void {
    switch (expr) {
        .rational => |value| if (value.denominator == 0) return error.InvalidRational,
        .parameter => |id| if (!hasParameter(d, id)) return error.DanglingParameter,
        .field_label => |ref| try validateLabelRef(d, ref.field, ref.label),
        .add => |pair| {
            if (pair.left >= index or pair.right >= index) return error.DanglingMetadata;
        },
        .mul => |pair| {
            if (pair.left >= index or pair.right >= index) return error.DanglingMetadata;
        },
        .bilinear => |item| {
            if (item.left >= index or item.right >= index) return error.DanglingMetadata;
            if (!hasSymbol(d, item.form_symbol)) return error.DanglingSymbol;
        },
    }
}

fn labelRole(d: Descriptor, ref: LabelRef, left_field: Id, right_field: Id) !LabelRole {
    const field_id = if (ref.side == .left) left_field else right_field;
    if (!hasField(d, field_id)) return error.DanglingField;
    const label = fieldLabel(d.fields[field_id], ref.slot) orelse return error.DanglingLabel;
    return label.role;
}

fn validateTensor(d: Descriptor, tensor: TensorFactor, left_field: Id, right_field: Id) !void {
    switch (tensor) {
        .none => {},
        .metric => |item| {
            if (try labelRole(d, item.left, left_field, right_field) != .vector_index) return error.IncompatibleLabelRole;
            if (try labelRole(d, item.right, left_field, right_field) != .vector_index) return error.IncompatibleLabelRole;
        },
        .momentum_index => |item| {
            if (try labelRole(d, item.momentum, left_field, right_field) != .momentum) return error.IncompatibleLabelRole;
            if (try labelRole(d, item.index, left_field, right_field) != .vector_index) return error.IncompatibleLabelRole;
        },
        .momentum_pair => |item| {
            if (try labelRole(d, item.left, left_field, right_field) != .momentum) return error.IncompatibleLabelRole;
            if (try labelRole(d, item.right, left_field, right_field) != .momentum) return error.IncompatibleLabelRole;
        },
    }
}

fn validateAction(d: Descriptor, action: ActionFactor, left_field: Id, right_field: Id) !void {
    switch (action) {
        .profile_derivative => |item| {
            if (try labelRole(d, item.profile, left_field, right_field) != .profile) return error.IncompatibleLabelRole;
            if (try labelRole(d, item.index, left_field, right_field) != .vector_index) return error.IncompatibleLabelRole;
        },
    }
}

fn validateIndexConstraint(d: Descriptor, row: PairIndexConstraintRow, left_field: Id, right_field: Id) !void {
    if (try labelRole(d, .{ .side = .left, .slot = row.left_slot }, left_field, right_field) != .vector_index) return error.IncompatibleLabelRole;
    if (try labelRole(d, .{ .side = .right, .slot = row.right_slot }, left_field, right_field) != .vector_index) return error.IncompatibleLabelRole;
}

/// validateDescriptor rejects malformed generated descriptor data.
pub fn validateDescriptor(d: Descriptor) !void {
    if (d.abi_version != descriptor_abi_version) return error.UnsupportedDescriptorAbi;
    if (!hasSymbol(d, d.theory_symbol)) return error.DanglingSymbol;
    if (d.reserved.ope_rules != 0 or d.reserved.operator_templates != 0 or d.reserved.relation_rules != 0 or d.reserved.basis_rules != 0) {
        return error.UnsupportedReservedService;
    }

    try denseUniqueIds(Parameter, d.parameters);
    try denseUniqueIds(QuantumNumber, d.quantum_numbers);
    try denseUniqueIds(Surface, d.surfaces);
    try denseUniqueIds(Field, d.fields);

    for (d.parameters) |parameter| {
        if (!hasSymbol(d, parameter.symbol)) return error.DanglingSymbol;
    }
    for (d.quantum_numbers) |number| {
        if (!hasSymbol(d, number.symbol)) return error.DanglingSymbol;
        if (number.group_symbol) |symbol| if (!hasSymbol(d, symbol)) return error.DanglingSymbol;
    }
    for (d.field_quantum_numbers) |item| {
        if (!hasField(d, item.field)) return error.DanglingField;
        if (!hasQuantumNumber(d, item.quantum_number)) return error.DanglingQuantumNumber;
        const number = d.quantum_numbers[item.quantum_number];
        switch (item.value) {
            .integer => if (number.kind != .u1_charge) return error.IncompatibleQuantumNumberValue,
            .rational => |value| {
                if (number.kind != .u1_charge) return error.IncompatibleQuantumNumberValue;
                if (value.denominator == 0) return error.InvalidRational;
            },
            .symbol => |symbol| {
                if (number.kind != .ade_irrep) return error.IncompatibleQuantumNumberValue;
                if (!hasSymbol(d, symbol)) return error.DanglingSymbol;
            },
        }
    }
    for (d.surfaces) |surface| {
        if (surface.modular_parameter) |id| if (!hasParameter(d, id)) return error.DanglingParameter;
    }
    for (d.fields) |field| {
        if (!hasSymbol(d, field.symbol)) return error.DanglingSymbol;
        try denseUniqueIds(LabelSchema, field.labels);
        for (field.labels) |label| if (!hasSymbol(d, label.symbol)) return error.DanglingSymbol;
        if (field.weight) |id| if (id >= d.metadata.len) return error.DanglingMetadata;
        if (field.anti_weight) |id| if (id >= d.metadata.len) return error.DanglingMetadata;
    }
    for (d.metadata, 0..) |expr, index| try validateMetadata(d, @intCast(index), expr);

    for (d.wick_rules) |rule| {
        if (!hasSurface(d, rule.surface)) return error.DanglingSurface;
        if (!hasField(d, rule.left) or !hasField(d, rule.right)) return error.DanglingField;
        if (rule.terms.len == 0) return error.EmptyWickRule;
        for (rule.index_constraints) |row| try validateIndexConstraint(d, row, rule.left, rule.right);
        const left_arity = d.fields[rule.left].labels.len;
        const right_arity = d.fields[rule.right].labels.len;
        for (rule.terms) |term| {
            for (term.scalars) |scalar| switch (scalar) {
                .parameter, .neg_parameter_half, .neg_i_parameter_half, .parameter_half => |id| if (!hasParameter(d, id)) return error.DanglingParameter,
                else => {},
            };
            for (term.tensors) |tensor| try validateTensor(d, tensor, rule.left, rule.right);
            for (term.actions) |action| try validateAction(d, action, rule.left, rule.right);
            for (term.residuals) |_| {}
        }
        if (left_arity != d.fields[rule.left].labels.len or right_arity != d.fields[rule.right].labels.len) return error.InvalidFieldArity;
    }

    for (d.zero_modes) |rule| {
        if (!hasSurface(d, rule.surface)) return error.DanglingSurface;
        if (rule.consumes.len == 0) return error.EmptyZeroMode;
        for (rule.consumes) |field_id| {
            if (!hasField(d, field_id)) return error.DanglingField;
            if (!d.fields[field_id].zero_mode_consumable) return error.IncompatibleZeroModeField;
        }
    }
}

fn stableId(seed: u32, local: u32) u32 {
    var hash = seed ^ 2166136261;
    hash = (hash ^ local) *% 16777619;
    return if (hash == 0) 1 else hash;
}

fn kindId(comptime d: Descriptor, field: Id) operators.OperatorKindId {
    return stableId(d.theory_hash, field + 1);
}

fn sectorId(comptime d: Descriptor, surface: Id, zero_rule: usize) zero_mode.Sector {
    return stableId(d.theory_hash ^ 0x51f1_0000, (@as(u32, surface) << 16) | @as(u32, @intCast(zero_rule + 1)));
}

fn lowerSupport(shape: InsertionShape) wick.Support {
    return switch (shape) {
        .single => .holomorphic,
        .pair => .bulk_pair,
    };
}

fn lowerInsertion(shape: InsertionShape) declare.Spec.InsertionShape {
    return switch (shape) {
        .single => .single,
        .pair => .pair,
    };
}

fn lowerLabelKind(role: LabelRole) declare.Spec.LabelKind {
    return switch (role) {
        .vector_index => .index,
        .momentum => .momentum,
        .profile => .profile,
        .scalar_parameter, .modular_parameter => @compileError("parameter roles are not field-label runtime slots"),
    };
}

fn lowerField(comptime d: Descriptor, comptime field: Field) declare.Spec.Operator {
    comptime var labels: [field.labels.len]declare.Spec.LabelKind = undefined;
    inline for (field.labels, 0..) |label, index| labels[index] = lowerLabelKind(label.role);
    return .{
        .name = d.symbols[field.symbol],
        .kind = kindId(d, field.id),
        .support = lowerSupport(field.insertion),
        .insertion = lowerInsertion(field.insertion),
        .labels = &labels,
        .statistics = if (field.statistics == .fermionic) .fermionic else .bosonic,
        .zero_mode_consumable = field.zero_mode_consumable,
    };
}

fn lowerSide(side: Side) wick.Side {
    return if (side == .left) .left else .right;
}

fn lowerCoordSlot(slot: CoordinateSlot) wick.CoordinateSlot {
    return switch (slot) {
        .position => .position,
        .holomorphic => .holomorphic,
        .antiholomorphic => .antiholomorphic,
    };
}

fn lowerCoordRef(ref: CoordinateRef) wick.CoordinateRef {
    return wick.coord(lowerSide(ref.side), lowerCoordSlot(ref.slot));
}

fn lowerLabelRef(ref: LabelRef) wick.LabelRef {
    return wick.label(lowerSide(ref.side), @intCast(ref.slot));
}

fn lowerIndexConstraint(row: PairIndexConstraintRow) wick.PairIndexConstraintRow {
    return .{
        .left_slot = @intCast(row.left_slot),
        .right_slot = @intCast(row.right_slot),
        .constraint = switch (row.constraint) {
            .none => .none,
            .same_sort => .same_sort,
            .conjugate_complex_sort => .conjugate_complex_sort,
        },
    };
}

fn lowerDerivative(left: bool, right: bool) wick.DerivativeAction {
    return .{ .include_left = left, .include_right = right };
}

fn parameterScalar(comptime d: Descriptor, id: Id) @TypeOf(scalars.one()) {
    return scalars.atomScalar(parameterAtom(d, id));
}

fn parameterAtom(comptime d: Descriptor, id: Id) u32 {
    return stableId(d.theory_hash ^ 0xa170_0000, id + 1);
}

fn lowerScalar(comptime d: Descriptor, factor: ScalarFactor) wick.ScalarFactor {
    return switch (factor) {
        .one => wick.scalar(scalars.one()),
        .rational => |value| wick.scalar(scalars.rational(value.numerator, value.denominator)),
        .parameter => |id| wick.scalar(parameterScalar(d, id)),
        .neg_parameter_half => |id| wick.scalar(scalars.div(scalars.neg(parameterScalar(d, id)), 2)),
        .neg_i_parameter_half => |id| wick.scalar(scalars.div(scalars.neg(scalars.i(parameterScalar(d, id))), 2)),
        .parameter_half => |id| wick.scalar(scalars.div(parameterScalar(d, id), 2)),
    };
}

fn lowerScalarValue(comptime d: Descriptor, factor: ScalarFactor) @TypeOf(scalars.one()) {
    return switch (lowerScalar(d, factor)) {
        .value => |value| value,
        else => @compileError("descriptor zero-mode normalization must be a value scalar"),
    };
}

fn lowerCoordinate(comptime d: Descriptor, factor: CoordinateFactor) wick.CoordinateFactor {
    return switch (factor) {
        .difference_power => |item| wick.differentiatedPower(
            wick.difference(lowerCoordRef(item.left), lowerCoordRef(item.right)),
            item.exponent,
            lowerDerivative(item.derive_left, item.derive_right),
        ),
        .logarithm => |item| wick.differentiatedLogarithm(
            wick.difference(lowerCoordRef(item.left), lowerCoordRef(item.right)),
            lowerDerivative(item.derive_left, item.derive_right),
        ),
        .named_kernel => |item| wick.differentiatedGreenKernel(
            d.symbols[item.symbol],
            wick.difference(lowerCoordRef(item.left), lowerCoordRef(item.right)),
            lowerDerivative(item.derive_left, item.derive_right),
        ),
        .green_exponential => |item| .{ .green_exponential = wick.difference(lowerCoordRef(item.left), lowerCoordRef(item.right)) },
    };
}

fn lowerTensor(factor: TensorFactor) wick.TensorFactor {
    return switch (factor) {
        .none => .none,
        .metric => |item| .{ .metric = .{ .left = lowerLabelRef(item.left), .right = lowerLabelRef(item.right) } },
        .momentum_index => |item| .{ .momentum_index = .{ .momentum = lowerLabelRef(item.momentum), .index = lowerLabelRef(item.index) } },
        .momentum_pair => |item| .{ .momentum_pair = .{ .left = lowerLabelRef(item.left), .right = lowerLabelRef(item.right) } },
    };
}

fn lowerAction(factor: ActionFactor) wick.ActionFactor {
    return switch (factor) {
        .profile_derivative => |item| wick.profileDerivative(lowerLabelRef(item.profile), lowerLabelRef(item.index)),
    };
}

fn LoweredTerm(comptime d: Descriptor, comptime term: WickTerm) type {
    return struct {
        const scalar_storage = blk: {
            var storage: [term.scalars.len]wick.ScalarFactor = undefined;
            for (term.scalars, 0..) |factor, index| storage[index] = lowerScalar(d, factor);
            break :blk storage;
        };
        const coordinate_storage = blk: {
            var storage: [term.coordinates.len]wick.CoordinateFactor = undefined;
            for (term.coordinates, 0..) |factor, index| storage[index] = lowerCoordinate(d, factor);
            break :blk storage;
        };
        const tensor_storage = blk: {
            var storage: [term.tensors.len]wick.TensorFactor = undefined;
            for (term.tensors, 0..) |factor, index| storage[index] = lowerTensor(factor);
            break :blk storage;
        };
        const action_storage = blk: {
            var storage: [term.actions.len]wick.ActionFactor = undefined;
            for (term.actions, 0..) |factor, index| storage[index] = lowerAction(factor);
            break :blk storage;
        };
        const residual_storage = blk: {
            var storage: [term.residuals.len]wick.Side = undefined;
            for (term.residuals, 0..) |side, index| storage[index] = lowerSide(side);
            break :blk storage;
        };
        const value = wick.termWithResiduals(&scalar_storage, &coordinate_storage, &tensor_storage, &action_storage, &residual_storage);
    };
}

fn LoweredWickRule(comptime d: Descriptor, comptime rule: WickRule) type {
    return struct {
        const terms = blk: {
            var storage: [rule.terms.len]wick.Term = undefined;
            for (rule.terms, 0..) |term, index| storage[index] = LoweredTerm(d, term).value;
            break :blk storage;
        };
        const constraint_storage = blk: {
            var storage: [rule.index_constraints.len]wick.PairIndexConstraintRow = undefined;
            for (rule.index_constraints, 0..) |row, index| storage[index] = lowerIndexConstraint(row);
            break :blk storage;
        };
        const value = wick.constrainedRule(
            wick.pattern(kindId(d, rule.left), lowerSupport(d.fields[rule.left].insertion)),
            wick.pattern(kindId(d, rule.right), lowerSupport(d.fields[rule.right].insertion)),
            wick.expr(&terms),
            &constraint_storage,
        );
    };
}

fn lowerWickRule(comptime d: Descriptor, comptime rule: WickRule) wick.Rule {
    return LoweredWickRule(d, rule).value;
}

fn lowerConsumeKinds(comptime d: Descriptor, comptime consumes: []const Id) [consumes.len]operators.OperatorKindId {
    var storage: [consumes.len]operators.OperatorKindId = undefined;
    inline for (consumes, 0..) |field_id, index| storage[index] = kindId(d, field_id);
    return storage;
}

fn LoweredZeroMode(comptime d: Descriptor, comptime rule: ZeroModeRule, comptime index: usize) type {
    return struct {
        const consume_storage = lowerConsumeKinds(d, rule.consumes);
        const sector = sectorId(d, rule.surface, index);
        const value = switch (rule.kind) {
            .constant_fermion => zero_mode.rule(sector, .{ .constant_fermion = .{
                .support = .sphere_holomorphic,
                .fermion_kind_ids = &consume_storage,
                .normalization = lowerScalarValue(d, rule.normalization),
            } }),
            .top_form_fermion => zero_mode.rule(sector, .{ .top_form_fermion = .{
                .support = .sphere_holomorphic,
                .field_kind_ids = &consume_storage,
                .normalization = lowerScalarValue(d, rule.normalization),
            } }),
            .boson_momentum_conservation => zero_mode.rule(sector, .{ .boson_momentum_conservation = .{
                .exp_kind_ids = &consume_storage,
                .profile_kind_ids = &.{},
                .normalization = .{
                    .scalar = lowerScalarValue(d, rule.normalization),
                    .two_pi_power = if (rule.two_pi_power == 0) .none else .{ .literal = rule.two_pi_power },
                },
            } }),
        };
    };
}

fn lowerZeroMode(comptime d: Descriptor, comptime rule: ZeroModeRule, comptime index: usize) zero_mode.Rule {
    return LoweredZeroMode(d, rule, index).value;
}

fn fieldSpecStorage(comptime d: Descriptor) [d.fields.len]declare.Spec.Operator {
    var storage: [d.fields.len]declare.Spec.Operator = undefined;
    inline for (d.fields, 0..) |field, index| storage[index] = lowerField(d, field);
    return storage;
}

fn wickStorage(comptime d: Descriptor) [d.wick_rules.len]wick.Rule {
    var storage: [d.wick_rules.len]wick.Rule = undefined;
    inline for (d.wick_rules, 0..) |rule, index| storage[index] = lowerWickRule(d, rule);
    return storage;
}

fn zeroStorage(comptime d: Descriptor) [d.zero_modes.len]zero_mode.Rule {
    var storage: [d.zero_modes.len]zero_mode.Rule = undefined;
    inline for (d.zero_modes, 0..) |rule, index| storage[index] = lowerZeroMode(d, rule, index);
    return storage;
}

fn fermionStorage(comptime fields: []const Field, comptime d: Descriptor) [fermionCount(fields)]operators.OperatorKindId {
    var storage: [fermionCount(fields)]operators.OperatorKindId = undefined;
    comptime var index: usize = 0;
    inline for (fields) |field| {
        if (field.statistics == .fermionic) {
            storage[index] = kindId(d, field.id);
            index += 1;
        }
    }
    return storage;
}

fn fermionCount(comptime fields: []const Field) usize {
    comptime var count: usize = 0;
    inline for (fields) |field| {
        if (field.statistics == .fermionic) count += 1;
    }
    return count;
}

/// ResultEventKind names one streamed Lisp-facing result event.
pub const ResultEventKind = enum(u8) {
    sum_term_begin,
    sum_term_end,
    wick_term_begin,
    wick_term_end,
    scalar,
    coordinate,
    tensor,
    zero_mode,
    residual_operator,
};

/// ResultEvent is one compact streamed result record.
pub const ResultEvent = struct {
    kind: ResultEventKind,
    a: u32 = 0,
    b: u32 = 0,
    c: u32 = 0,
    d: i32 = 0,
    name: ?[]const u8 = null,
};

/// StreamFn consumes one result event and user payload.
pub const StreamFn = *const fn (*anyopaque, ResultEvent) anyerror!void;

const CountSink = struct {
    count: usize = 0,

    pub fn emitWickBranchSign(_: *@This(), _: i8) !void {}
    pub fn emitWickTermStart(_: *@This(), _: anytype) !void {}
    pub fn emitWickScalar(_: *@This(), _: anytype) !void {}
    pub fn emitWickCoordinate(_: *@This(), _: anytype) !void {}
    pub fn emitWickTensor(_: *@This(), _: anytype) !void {}
    pub fn emitWickAction(_: *@This(), _: anytype) !void {}
    pub fn emitWickResidualOperator(_: *@This(), _: anytype) !void {}
    pub fn emitWickTermEnd(_: *@This()) !void {}
    pub fn emitZeroModeFactor(_: *@This(), _: anytype) !void {}
    pub fn emitZeroModeBaseEnd(self: *@This()) !void {
        self.count += 1;
    }
};

fn labelSymbol(value: kernel.Call.LabelValue) u32 {
    return switch (value) {
        .symbol => |symbol| symbol,
        .integer => |item| @intCast(item),
        .rational => 0,
        .tensor => |item| item,
    };
}

fn scalarFlags(imaginary_power: u2, atom_power: i8) u32 {
    return @as(u32, imaginary_power) | (@as(u32, @as(u8, @bitCast(atom_power))) << 8);
}

fn scalarValueEvent(rational: anytype, imaginary_power: u2, atom: ?u32, atom_power: i8) !ResultEvent {
    const numerator = std.math.cast(i32, rational.numerator) orelse return error.ScalarNumeratorOutOfRange;
    const denominator = std.math.cast(u32, rational.denominator) orelse return error.ScalarDenominatorOutOfRange;
    return .{
        .kind = .scalar,
        .a = atom orelse 0,
        .b = denominator,
        .c = scalarFlags(imaginary_power, atom_power),
        .d = numerator,
        .name = "scalar-monomial",
    };
}

fn scalarEvent(value: anytype) !ResultEvent {
    return switch (value) {
        .one => .{ .kind = .scalar },
        .rational => |rational| scalarValueEvent(rational, 0, null, 0),
        .monomial => |monomial| scalarValueEvent(monomial.rational, monomial.imaginary_power, monomial.atom, monomial.atom_power),
    };
}

const EventSink = struct {
    payload: *anyopaque,
    stream: StreamFn,

    fn emit(self: *@This(), event: ResultEvent) !void {
        try self.stream(self.payload, event);
    }

    pub fn emitWickBranchSign(self: *@This(), sign: i8) !void {
        if (sign < 0) try self.emit(.{ .kind = .scalar, .d = -1 });
    }

    pub fn emitWickTermStart(self: *@This(), event: anytype) !void {
        try self.emit(.{ .kind = .wick_term_begin, .a = @intCast(event.left_index), .b = @intCast(event.right_index), .c = @intCast(event.term_index) });
    }

    pub fn emitWickScalar(self: *@This(), factor: anytype) !void {
        switch (factor) {
            .value => |value| try self.emit(try scalarEvent(value)),
            .label_bilinear_phase => |item| try self.emit(.{ .kind = .scalar, .a = labelSymbol(item.left), .b = labelSymbol(item.right), .name = item.form }),
            .cocycle => |item| try self.emit(.{ .kind = .scalar, .a = labelSymbol(item.left), .b = labelSymbol(item.right), .name = item.table }),
            .spin_structure => |name| try self.emit(.{ .kind = .scalar, .name = name }),
        }
    }

    pub fn emitWickCoordinate(self: *@This(), factor: anytype) !void {
        switch (factor.kernel) {
            .difference_power => |item| try self.emit(.{ .kind = .coordinate, .a = item.coordinate.left, .b = item.coordinate.right, .d = item.exponent }),
            .logarithm => |item| try self.emit(.{ .kind = .coordinate, .a = item.left, .b = item.right, .name = "log" }),
            .green_kernel => |item| try self.emit(.{ .kind = .coordinate, .a = item.coordinate.left, .b = item.coordinate.right, .name = item.name }),
            .green_exponential => |item| try self.emit(.{ .kind = .coordinate, .a = item.left, .b = item.right, .name = "exp-green" }),
        }
    }

    pub fn emitWickTensor(self: *@This(), factor: anytype) !void {
        switch (factor) {
            .none => try self.emit(.{ .kind = .tensor }),
            .metric => |item| try self.emit(.{ .kind = .tensor, .a = labelSymbol(item.left), .b = labelSymbol(item.right), .name = "metric" }),
            .momentum_index => |item| try self.emit(.{ .kind = .tensor, .a = labelSymbol(item.momentum), .b = labelSymbol(item.index), .name = "momentum-index" }),
            .momentum_pair => |item| try self.emit(.{ .kind = .tensor, .a = labelSymbol(item.left), .b = labelSymbol(item.right), .name = "momentum-pair" }),
            else => try self.emit(.{ .kind = .tensor }),
        }
    }

    pub fn emitWickAction(self: *@This(), _: anytype) !void {
        try self.emit(.{ .kind = .residual_operator, .name = "action" });
    }

    pub fn emitWickResidualOperator(self: *@This(), residual: anytype) !void {
        try self.emit(.{ .kind = .residual_operator, .a = @intCast(residual.input_index) });
    }

    pub fn emitWickTermEnd(self: *@This()) !void {
        try self.emit(.{ .kind = .wick_term_end });
    }

    pub fn emitZeroModeFactor(self: *@This(), factor: anytype) !void {
        switch (factor) {
            .bc_top_form => try self.emit(.{ .kind = .zero_mode, .name = "bc-top-form" }),
            .eta_xi_zero_mode => |item| try self.emit(.{ .kind = .zero_mode, .a = item.xi.coordinate, .name = "eta-xi-zero-mode" }),
            .momentum_delta => |item| {
                try self.emit(try scalarEvent(item.scalar));
                try self.emit(.{ .kind = .zero_mode, .a = item.two_pi_power, .b = @intCast(item.momenta.len), .name = "momentum-delta" });
                for (item.momenta) |momentum| {
                    try self.emit(.{ .kind = .zero_mode, .a = labelSymbol(momentum), .name = "momentum-delta-momentum" });
                }
            },
            else => try self.emit(.{ .kind = .zero_mode }),
        }
    }

    pub fn emitZeroModeBaseEnd(self: *@This()) !void {
        try self.emit(.{ .kind = .sum_term_end });
    }
};

fn insertionFrom(shape: InsertionShape, coords: []const u32) !operators.OperatorInsertion {
    return switch (shape) {
        .single => if (coords.len == 1) .{ .single = .{ .position = coords[0], .derivatives = 0 } } else error.InvalidCoordinateArity,
        .pair => if (coords.len == 2) .{ .pair = .{
            .holomorphic_position = coords[0],
            .antiholomorphic_position = coords[1],
            .holomorphic_derivatives = 0,
            .antiholomorphic_derivatives = 0,
        } } else error.InvalidCoordinateArity,
    };
}

fn singleInsertion(z: u32, derivatives: u8) operators.OperatorInsertion {
    return .{ .single = .{ .position = z, .derivatives = derivatives } };
}

fn pairInsertion(z: u32, zbar: u32) operators.OperatorInsertion {
    return .{ .pair = .{
        .holomorphic_position = z,
        .antiholomorphic_position = zbar,
        .holomorphic_derivatives = 0,
        .antiholomorphic_derivatives = 0,
    } };
}

fn tokenId(value: anytype) u32 {
    const T = @TypeOf(value);
    return switch (@typeInfo(T)) {
        .int, .comptime_int => @intCast(value),
        .@"enum" => @intFromEnum(value),
        else => @compileError("generated field labels and coordinates must be integer-like tokens"),
    };
}

fn labelTupleCount(comptime Labels: type) comptime_int {
    const info = @typeInfo(Labels);
    if (info != .@"struct" or !info.@"struct".is_tuple) @compileError("generated field labels must be passed as a tuple");
    return info.@"struct".fields.len;
}

fn fillLabelSymbols(comptime count: usize, out: *[count]u32, labels: anytype) void {
    inline for (0..count) |index| out[index] = tokenId(labels[index]);
}

fn fieldIdByName(comptime d: Descriptor, comptime name: []const u8) Id {
    inline for (d.fields) |field| {
        if (std.mem.eql(u8, d.symbols[field.symbol], name)) return field.id;
    }
    @compileError("unknown generated field name");
}

fn GeneratedField(comptime d: Descriptor, comptime field_id: Id) type {
    const field = d.fields[field_id];
    return struct {
        /// id is the descriptor field id for this generated field builder.
        pub const id = field_id;
        /// name is the descriptor symbol for this generated field builder.
        pub const name = d.symbols[field.symbol];

        /// single appends a single-coordinate generated field insertion.
        pub fn single(local: anytype, z: anytype, derivatives: u8, labels: anytype) !void {
            if (field.insertion != .single) return error.InvalidInsertionShape;
            const count = comptime labelTupleCount(@TypeOf(labels));
            if (count != field.labels.len) return error.InvalidFieldArity;
            var label_symbols: [count]u32 = undefined;
            fillLabelSymbols(count, &label_symbols, labels);
            try local.insertFieldRaw(field_id, singleInsertion(tokenId(z), derivatives), &label_symbols);
        }

        /// pair appends a bulk-pair generated field insertion.
        pub fn pair(local: anytype, z: anytype, zbar: anytype, labels: anytype) !void {
            if (field.insertion != .pair) return error.InvalidInsertionShape;
            const count = comptime labelTupleCount(@TypeOf(labels));
            if (count != field.labels.len) return error.InvalidFieldArity;
            var label_symbols: [count]u32 = undefined;
            fillLabelSymbols(count, &label_symbols, labels);
            try local.insertFieldRaw(field_id, pairInsertion(tokenId(z), tokenId(zbar)), &label_symbols);
        }
    };
}

fn hasSingleSurfaceKind(comptime d: Descriptor, comptime kind: SurfaceKind) bool {
    return d.surfaces.len == 1 and d.surfaces[0].kind == kind;
}

fn GeneratedConfig(comptime d: Descriptor, comptime Config: type) type {
    if (hasSingleSurfaceKind(d, .sphere)) {
        return struct {
            /// default selects all lowered descriptor rules.
            pub const default = Config{};
            /// sphere selects the generated sphere rule set.
            pub const sphere = default;
        };
    }
    if (hasSingleSurfaceKind(d, .torus)) {
        return struct {
            /// default selects all lowered descriptor rules.
            pub const default = Config{};
            /// torus selects the generated torus rule set.
            pub const torus = default;
        };
    }
    return struct {
        /// default selects all lowered descriptor rules.
        pub const default = Config{};
    };
}

/// GeneratedTheory lowers one descriptor to an executable theory boundary.
pub fn GeneratedTheory(comptime d: Descriptor) type {
    comptime {
        validateDescriptor(d) catch |err| @compileError(@errorName(err));
    }
    const rules = wickStorage(d);
    const zeros = zeroStorage(d);
    const fermions = fermionStorage(d.fields, d);
    const Config = declare.correlatorConfig(.{
        .wick_rules = &rules,
        .zero_modes = &zeros,
        .fermion_kinds = &fermions,
    });

    return struct {
        /// abi_version is the descriptor ABI accepted by this generated theory.
        pub const abi_version = descriptor_abi_version;
        /// theory_hash distinguishes generated theories at runtime.
        pub const theory_hash = d.theory_hash;
        /// descriptor exposes the compact source descriptor for audits.
        pub const descriptor = d;
        /// config exposes generated correlator configs through the theory API.
        pub const config = GeneratedConfig(d, Config);

        /// op groups compile-time generated field builders.
        pub const op = struct {
            /// field returns a builder for a descriptor field name.
            pub fn field(comptime name: []const u8) type {
                return GeneratedField(d, fieldIdByName(d, name));
            }
        };

        /// field returns a builder for a descriptor field name.
        pub fn field(comptime name: []const u8) type {
            return GeneratedField(d, fieldIdByName(d, name));
        }

        /// Context owns symbols and a single mutable operator list.
        pub const Context = struct {
            allocator: std.mem.Allocator,
            symbols: std.ArrayList([]u8) = .empty,
            labels: std.ArrayList(kernel.Call.LabelValue) = .empty,
            operators_list: std.ArrayList(kernel.Call.LocalOp) = .empty,
            frozen_labels: []kernel.Call.LabelValue = &.{},
            frozen_ops: []kernel.Call.LocalOp = &.{},
            label_store: kernel.Call.LabelStore = .{ .values = &.{} },
            next_normal_order_group: normal_ordering.Group = normal_ordering.first,

            /// init creates an empty generated-theory context.
            pub fn init(allocator: std.mem.Allocator) Context {
                return .{ .allocator = allocator };
            }

            /// deinit releases context-owned buffers.
            pub fn deinit(self: *Context) void {
                for (self.symbols.items) |name| self.allocator.free(name);
                self.symbols.deinit(self.allocator);
                self.labels.deinit(self.allocator);
                self.operators_list.deinit(self.allocator);
                self.allocator.free(self.frozen_labels);
                self.allocator.free(self.frozen_ops);
            }

            /// intern returns a stable context-local symbol id for a name.
            pub fn intern(self: *Context, name: []const u8) !u32 {
                for (self.symbols.items, 1..) |stored, symbol_index| {
                    if (std.mem.eql(u8, stored, name)) return @intCast(symbol_index);
                }
                const copy = try self.allocator.dupe(u8, name);
                try self.symbols.append(self.allocator, copy);
                return @intCast(self.symbols.items.len);
            }

            /// symbolName resolves a context-local symbol id.
            pub fn symbolName(self: *const Context, token: u32) ?[]const u8 {
                if (token == 0 or token > self.symbols.items.len) return null;
                return self.symbols.items[token - 1];
            }

            /// symbol interns a generic runtime token name.
            pub fn symbol(self: *Context, name: []const u8) !u32 {
                return self.intern(name);
            }

            /// coord interns a coordinate token name.
            pub fn coord(self: *Context, name: []const u8) !u32 {
                return self.intern(name);
            }

            /// index interns an index token name.
            pub fn index(self: *Context, name: []const u8) !u32 {
                return self.intern(name);
            }

            /// momentum interns a momentum token name.
            pub fn momentum(self: *Context, name: []const u8) !u32 {
                return self.intern(name);
            }

            /// profile interns a profile token name.
            pub fn profile(self: *Context, name: []const u8) !u32 {
                return self.intern(name);
            }

            /// insertFieldRaw appends one already-shaped generated field occurrence.
            pub fn insertFieldRaw(self: *Context, field_id: Id, insertion: operators.OperatorInsertion, label_symbols: []const u32) !void {
                if (field_id >= d.fields.len) return error.DanglingField;
                const field_info = d.fields[field_id];
                if (label_symbols.len != field_info.labels.len) return error.InvalidFieldArity;
                const label_start = self.labels.items.len;
                for (label_symbols) |label_symbol| {
                    try self.labels.append(self.allocator, .{ .symbol = label_symbol });
                }
                try self.operators_list.append(self.allocator, .{
                    .insertion = insertion,
                    .kind = kindId(d, field_id),
                    .labels = @intCast(label_start),
                });
            }

            /// insertField appends one generated field occurrence.
            pub fn insertField(self: *Context, field_id: Id, coords: []const u32, label_symbols: []const u32) !void {
                if (field_id >= d.fields.len) return error.DanglingField;
                const field_info = d.fields[field_id];
                try self.insertFieldRaw(field_id, try insertionFrom(field_info.insertion, coords), label_symbols);
            }

            /// normalOrderLast tags the last count insertions as one normal product.
            pub fn normalOrderLast(self: *Context, count: usize) !void {
                try normal_ordering.tagLast(self.operators_list.items, count, &self.next_normal_order_group);
            }

            /// freeze returns the current immutable operator sequence.
            pub fn freeze(self: *Context) !kernel.Call.MultiOp {
                self.allocator.free(self.frozen_labels);
                self.allocator.free(self.frozen_ops);
                self.frozen_labels = try self.labels.toOwnedSlice(self.allocator);
                self.frozen_ops = try self.operators_list.toOwnedSlice(self.allocator);
                self.label_store = .{ .values = self.frozen_labels };
                return .{ .operators = self.frozen_ops, .labels = &self.label_store };
            }

            /// ops freezes the current generated operator list.
            pub fn ops(self: *Context) !kernel.Call.MultiOp {
                return self.freeze();
            }
        };

        /// local constructs a value-style generated-theory operator builder.
        pub fn local(allocator: std.mem.Allocator) Context {
            return Context.init(allocator);
        }

        /// descriptorAbiVersion returns the generated descriptor ABI version.
        pub fn descriptorAbiVersion() u32 {
            return abi_version;
        }

        /// theoryHash returns the generated theory hash.
        pub fn theoryHash() u32 {
            return theory_hash;
        }

        /// scalarAtomParameterName resolves a descriptor parameter scalar atom.
        pub fn scalarAtomParameterName(atom: u32) ?[]const u8 {
            inline for (d.parameters) |parameter| {
                if (parameterAtom(d, parameter.id) == atom) return d.symbols[parameter.symbol];
            }
            return null;
        }

        /// contextCreate allocates a generated-theory context.
        pub fn contextCreate(allocator: std.mem.Allocator) !*Context {
            const ctx = try allocator.create(Context);
            ctx.* = Context.init(allocator);
            return ctx;
        }

        /// contextDestroy releases a generated-theory context.
        pub fn contextDestroy(ctx: *Context) void {
            const allocator = ctx.allocator;
            ctx.deinit();
            allocator.destroy(ctx);
        }

        /// symbolIntern interns one runtime symbol name.
        pub fn symbolIntern(ctx: *Context, name: []const u8) !u32 {
            return ctx.intern(name);
        }

        /// fieldInsert appends one field occurrence.
        pub fn fieldInsert(ctx: *Context, field_id: Id, coords: []const u32, label_symbols: []const u32) !void {
            return ctx.insertField(field_id, coords, label_symbols);
        }

        /// normalOrdering tags the last count insertions as one normal product.
        pub fn normalOrdering(ctx: *Context, count: usize) !void {
            return ctx.normalOrderLast(count);
        }

        /// operatorListFreeze freezes the current operator list.
        pub fn operatorListFreeze(ctx: *Context) !kernel.Call.MultiOp {
            return ctx.freeze();
        }

        /// correlator streams generated-theory correlator output to a Zig sink.
        pub fn correlator(config_ptr: anytype, ops: kernel.Call.MultiOp, sink: anytype) !void {
            return shared.streamCorrelator(config_ptr, ops, sink);
        }

        /// correlatorCount returns the number of accepted streamed branches.
        pub fn correlatorCount(ops: kernel.Call.MultiOp) !usize {
            var sink = CountSink{};
            try shared.streamCorrelator(&config.default, ops, &sink);
            return sink.count;
        }

        /// correlatorRun streams result events through a caller-provided function.
        pub fn correlatorRun(ops: kernel.Call.MultiOp, payload: *anyopaque, stream: StreamFn) !void {
            var sink = EventSink{ .payload = payload, .stream = stream };
            try sink.emit(.{ .kind = .sum_term_begin });
            try shared.streamCorrelator(&config.default, ops, &sink);
        }
    };
}

test "generated theory exposes field builders and direct correlator sink" {
    const symbols = [_][]const u8{ "free-fermion-10", "spin10", "d5", "psi", "mu", "vector" };
    const quantum_numbers = [_]QuantumNumber{
        .{ .id = 0, .symbol = 1, .kind = .ade_irrep, .group_symbol = 2 },
    };
    const field_quantum_numbers = [_]FieldQuantumNumber{
        .{ .field = 0, .quantum_number = 0, .value = .{ .symbol = 5 } },
    };
    const surfaces = [_]Surface{
        .{ .id = 0, .kind = .sphere, .coordinate_model = .rational },
    };
    const fields = [_]Field{
        .{ .id = 0, .symbol = 3, .insertion = .single, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 4 }}, .statistics = .fermionic },
    };
    const terms = [_]WickTerm{
        .{
            .scalars = &.{.one},
            .coordinates = &.{.{ .difference_power = .{
                .left = .{ .side = .left, .slot = .position },
                .right = .{ .side = .right, .slot = .position },
                .exponent = -1,
                .derive_left = true,
                .derive_right = true,
            } }},
            .tensors = &.{.{ .metric = .{
                .left = .{ .side = .left, .slot = 0 },
                .right = .{ .side = .right, .slot = 0 },
            } }},
        },
    };
    const wick_rules = [_]WickRule{
        .{ .surface = 0, .left = 0, .right = 0, .terms = &terms },
    };
    const theory = GeneratedTheory(.{
        .theory_symbol = 0,
        .theory_hash = 0x1933f00d,
        .symbols = &symbols,
        .quantum_numbers = &quantum_numbers,
        .field_quantum_numbers = &field_quantum_numbers,
        .surfaces = &surfaces,
        .fields = &fields,
        .wick_rules = &wick_rules,
    });

    try std.testing.expect(comptime @hasDecl(theory.config, "default"));
    try std.testing.expect(comptime @hasDecl(theory.config, "sphere"));
    try std.testing.expectEqualStrings("psi", theory.field("psi").name);

    var local_ctx = theory.local(std.testing.allocator);
    defer local_ctx.deinit();
    const z0 = try local_ctx.coord("z0");
    const z1 = try local_ctx.coord("z1");
    const mu = try local_ctx.index("mu");
    const nu = try local_ctx.index("nu");

    const Psi = theory.field("psi");
    try Psi.single(&local_ctx, z0, 0, .{mu});
    try theory.op.field("psi").single(&local_ctx, z1, 0, .{nu});
    const ops = try local_ctx.ops();

    const Sink = struct {
        wick_terms: usize = 0,
        coordinates: usize = 0,
        tensors: usize = 0,
        base_cases: usize = 0,

        pub fn emitWickBranchSign(_: *@This(), _: i8) !void {}
        pub fn emitWickTermStart(self: *@This(), _: anytype) !void {
            self.wick_terms += 1;
        }
        pub fn emitWickScalar(_: *@This(), _: anytype) !void {}
        pub fn emitWickCoordinate(self: *@This(), _: anytype) !void {
            self.coordinates += 1;
        }
        pub fn emitWickTensor(self: *@This(), _: anytype) !void {
            self.tensors += 1;
        }
        pub fn emitWickAction(_: *@This(), _: anytype) !void {}
        pub fn emitWickResidualOperator(_: *@This(), _: anytype) !void {}
        pub fn emitWickTermEnd(_: *@This()) !void {}
        pub fn emitZeroModeFactor(_: *@This(), _: anytype) !void {}
        pub fn emitZeroModeBaseEnd(self: *@This()) !void {
            self.base_cases += 1;
        }
    };
    var sink = Sink{};
    try theory.correlator(&theory.config.sphere, ops, &sink);

    try std.testing.expectEqual(@as(usize, 1), sink.wick_terms);
    try std.testing.expectEqual(@as(usize, 1), sink.coordinates);
    try std.testing.expectEqual(@as(usize, 1), sink.tensors);
    try std.testing.expectEqual(@as(usize, 1), sink.base_cases);
}
