const std = @import("std");
const operators = @import("../expressions/operators.zig");
const coefficient = @import("../expressions/coefficient.zig");
const kernel = @import("../kernel.zig");
const normal_ordering = @import("../normal-ordering/normal-ordering.zig");
const theory = @import("../theory/theory.zig");
const wick_correlator = @import("../correlators/wick.zig");
const KernelOperatorList = kernel.Call.MultiOp;

/// LocalOperator is an opaque token for one operator insertion.
pub const LocalOperator = opaque {};

/// OperatorList is an opaque frozen operator sequence for correlator calls.
pub const OperatorList = opaque {};

/// Handle groups compact ids used by preset operator builders.
pub const Handle = struct {
    /// Coord names a holomorphic or antiholomorphic coordinate variable.
    pub const Coord = enum(u32) { _ };
    /// BoundaryCoord names a real boundary coordinate variable.
    pub const BoundaryCoord = enum(u32) { _ };
    /// Index names a target-space vector index.
    pub const Index = enum(u32) { _ };
    /// Momentum names a target-space momentum expression.
    pub const Momentum = enum(u32) { _ };
    /// Profile names a selected presentation of a target-space profile.
    pub const Profile = enum(u32) { _ };
    /// TargetFunction names a position-space target profile.
    pub const TargetFunction = enum(u32) { _ };
    /// FourierTransform names a Fourier-space target profile.
    pub const FourierTransform = enum(u32) { _ };
    /// TargetPoint names a point in target space.
    pub const TargetPoint = enum(u32) { _ };
    /// ProfileCoefficient names one coefficient in a polynomial profile.
    pub const ProfileCoefficient = enum(u32) { _ };
    /// TensorProjector names a tensor-code projector expression.
    pub const TensorProjector = enum(u32) { _ };
    /// BoundaryStack names stacked boundary-condition Chan-Paton data.
    pub const BoundaryStack = enum(u32) { _ };
    /// ProfilePresentation records how a profile handle should be lowered.
    pub const ProfilePresentation = enum(u2) {
        position_space,
        fourier,
        polynomial_rnc,
    };
};

fn rawToken(value: anytype) u32 {
    return @intFromEnum(value);
}

fn token(comptime T: type, id: u32) T {
    return @enumFromInt(if (id == 0) 1 else id);
}

const profile_tag_shift = 30;
const profile_payload_mask: u32 = 0x3fff_ffff;

/// profileHandle packs a profile presentation tag with a compact payload id.
pub fn profileHandle(comptime presentation: Handle.ProfilePresentation, payload: u32) Handle.Profile {
    const tag = @as(u32, @intFromEnum(presentation)) << profile_tag_shift;
    return token(Handle.Profile, tag | (payload & profile_payload_mask));
}

fn profilePresentation(profile: Handle.Profile) Handle.ProfilePresentation {
    return @enumFromInt(@intFromEnum(profile) >> profile_tag_shift);
}

fn profilePayload(profile: Handle.Profile) u32 {
    return @intFromEnum(profile) & profile_payload_mask;
}

fn stableId(comptime namespace: []const u8, comptime name: []const u8) u32 {
    var hash: u32 = 2166136261;
    inline for (namespace) |byte| {
        hash = (hash ^ @as(u32, byte)) *% 16777619;
    }
    hash = (hash ^ @as(u32, ':')) *% 16777619;
    inline for (name) |byte| {
        hash = (hash ^ @as(u32, byte)) *% 16777619;
    }
    return if (hash == 0) 1 else hash;
}

/// configRef derives a stable id for correlator configuration data.
fn configRef(comptime namespace: []const u8, comptime name: []const u8) ConfigRef {
    return stableId(namespace, name);
}

const ScalarAtom = u32;

const ConfigRef = u32;

const RationalScalar = struct {
    numerator: i64,
    denominator: i64,
};

const ScalarMonomial = struct {
    rational: RationalScalar = .{ .numerator = 1, .denominator = 1 },
    imaginary_power: u2 = 0,
    atom: ?ScalarAtom = null,
    atom_power: i8 = 0,
};

const RuleScalar = union(enum) {
    one,
    rational: RationalScalar,
    monomial: ScalarMonomial,
};

/// scalars exposes basic algebra for compact structured rule scalars.
const scalars = ScalarDsl;

const ScalarDsl = struct {
    fn absInt(value: i64) u64 {
        if (value == std.math.minInt(i64)) return @as(u64, 1) << 63;
        return if (value < 0) @intCast(-value) else @intCast(value);
    }

    fn gcd(first: u64, second: u64) u64 {
        var a = first;
        var b = second;
        while (b != 0) {
            const rem = a % b;
            a = b;
            b = rem;
        }
        return if (a == 0) 1 else a;
    }

    fn rationalValue(comptime numerator: i64, comptime denominator: i64) RationalScalar {
        if (denominator == 0) @compileError("rational denominator cannot be zero");
        var num = numerator;
        var den = denominator;
        if (den < 0) {
            num = -num;
            den = -den;
        }
        const factor: i64 = @intCast(gcd(absInt(num), absInt(den)));
        return .{
            .numerator = @divExact(num, factor),
            .denominator = @divExact(den, factor),
        };
    }

    /// atom derives a stable scalar atom id from a preset namespace and atom name.
    pub fn atom(comptime namespace: []const u8, comptime name: []const u8) ScalarAtom {
        return stableId(namespace, name);
    }

    /// one constructs the multiplicative unit scalar.
    pub fn one() RuleScalar {
        return .one;
    }

    /// rational constructs an exact rational scalar.
    pub fn rational(comptime numerator: i64, comptime denominator: i64) RuleScalar {
        return .{ .rational = rationalValue(numerator, denominator) };
    }

    /// atomScalar constructs a scalar consisting of one named atom.
    pub fn atomScalar(comptime atom_id: ScalarAtom) RuleScalar {
        return monomial(1, 1, 0, atom_id, 1);
    }

    /// monomial constructs a rational times i-power times atom-power scalar.
    pub fn monomial(comptime numerator: i64, comptime denominator: i64, comptime imaginary_power: u2, comptime atom_id: ?ScalarAtom, comptime atom_power: i8) RuleScalar {
        return .{ .monomial = .{
            .rational = rationalValue(numerator, denominator),
            .imaginary_power = imaginary_power,
            .atom = atom_id,
            .atom_power = atom_power,
        } };
    }

    fn monomialFrom(comptime value: RuleScalar) ScalarMonomial {
        return switch (value) {
            .one => .{},
            .rational => |r| .{ .rational = r },
            .monomial => |m| m,
        };
    }

    /// scale multiplies a scalar by an exact rational number.
    pub fn scale(comptime value: RuleScalar, comptime numerator: i64, comptime denominator: i64) RuleScalar {
        var factor = monomialFrom(value);
        factor.rational = rationalValue(factor.rational.numerator * numerator, factor.rational.denominator * denominator);
        return .{ .monomial = factor };
    }

    /// neg negates a scalar.
    pub fn neg(comptime value: RuleScalar) RuleScalar {
        return scale(value, -1, 1);
    }

    /// div divides a scalar by an integer denominator.
    pub fn div(comptime value: RuleScalar, comptime denominator: i64) RuleScalar {
        return scale(value, 1, denominator);
    }

    /// i multiplies a scalar by the imaginary unit.
    pub fn i(comptime value: RuleScalar) RuleScalar {
        var factor = monomialFrom(value);
        factor.imaginary_power +%= 1;
        return .{ .monomial = factor };
    }
};

/// familyKind derives a compact operator kind id from a preset namespace and local family enum.
fn familyKind(comptime namespace: []const u8, comptime family: anytype) operators.OperatorKindId {
    return stableId(namespace, @tagName(family));
}

/// sectorId derives a compact zero-mode sector id from a preset namespace and local sector enum.
fn sectorId(comptime namespace: []const u8, comptime sector: anytype) u32 {
    return stableId(namespace, @tagName(sector));
}

const LocalStateImpl = struct {
    allocator: std.mem.Allocator,
    labels: std.ArrayList(kernel.Call.LabelValue) = .empty,
    operators_list: std.ArrayList(kernel.Call.LocalOp) = .empty,
    pending_operators: std.ArrayList(*LocalOperatorImpl) = .empty,
    owned_labels: []kernel.Call.LabelValue = &.{},
    owned_operators: []kernel.Call.LocalOp = &.{},
    label_store: kernel.Call.LabelStore = .{ .values = &.{} },
    next_symbol: u32 = 1,
    next_normal_order_group: normal_ordering.Group = normal_ordering.first,
    finished: bool = false,
};

const LocalOperatorImpl = struct {
    owner: *LocalStateImpl,
    item: kernel.Call.LocalOp,
};

/// Local builds typed handles and freezes operator lists for correlator calls.
pub const Local = opaque {
    /// init constructs an empty local-operator builder.
    pub fn init(allocator: std.mem.Allocator) !*Local {
        const state = try allocator.create(LocalStateImpl);
        state.* = .{ .allocator = allocator };
        return @ptrCast(state);
    }

    fn data(self: *Local) *LocalStateImpl {
        return @ptrCast(@alignCast(self));
    }

    /// deinit releases memory owned by this local builder and its frozen operator list.
    pub fn deinit(self: *Local) void {
        const state = self.data();
        const allocator = state.allocator;
        if (state.finished) {
            allocator.free(state.owned_labels);
            allocator.free(state.owned_operators);
        } else {
            state.labels.deinit(allocator);
            state.operators_list.deinit(allocator);
        }
        for (state.pending_operators.items) |pending| {
            allocator.destroy(pending);
        }
        state.pending_operators.deinit(allocator);
        allocator.destroy(state);
    }

    fn next(self: *Local) u32 {
        const state = self.data();
        const value = state.next_symbol;
        state.next_symbol += 1;
        return value;
    }

    /// coord creates a named bulk coordinate token.
    pub fn coord(self: *Local, name: []const u8) !Handle.Coord {
        _ = name;
        return token(Handle.Coord, self.next());
    }

    /// boundaryCoord creates a named boundary coordinate token.
    pub fn boundaryCoord(self: *Local, name: []const u8) !Handle.BoundaryCoord {
        _ = name;
        return token(Handle.BoundaryCoord, self.next());
    }

    /// index creates a target-space index token.
    pub fn index(self: *Local, name: []const u8) !Handle.Index {
        _ = name;
        return token(Handle.Index, self.next());
    }

    /// momentum creates a target-space momentum token.
    pub fn momentum(self: *Local, name: []const u8) !Handle.Momentum {
        _ = name;
        return token(Handle.Momentum, self.next());
    }

    /// targetFunction creates a position-space target-profile token.
    pub fn targetFunction(self: *Local, name: []const u8) !Handle.TargetFunction {
        _ = name;
        return token(Handle.TargetFunction, self.next());
    }

    /// fourierTransform creates a Fourier-space profile token.
    pub fn fourierTransform(self: *Local, name: []const u8) !Handle.FourierTransform {
        _ = name;
        return token(Handle.FourierTransform, self.next());
    }

    /// targetPoint creates a target-space point token.
    pub fn targetPoint(self: *Local, name: []const u8) !Handle.TargetPoint {
        _ = name;
        return token(Handle.TargetPoint, self.next());
    }

    /// profileCoefficient creates a polynomial-profile coefficient token.
    pub fn profileCoefficient(self: *Local, name: []const u8) !Handle.ProfileCoefficient {
        _ = name;
        return token(Handle.ProfileCoefficient, self.next());
    }

    fn labelSpan(self: *Local, values: []const kernel.Call.LabelValue) !theory.Id.LabelSpan {
        const state = self.data();
        const start = state.labels.items.len;
        try state.labels.appendSlice(state.allocator, values);
        return @intCast(start);
    }

    fn symbol(value: anytype) kernel.Call.LabelValue {
        return .{ .symbol = rawToken(value) };
    }

    fn op(self: *Local, kind: operators.OperatorKindId, insertion: operators.OperatorInsertion, values: []const kernel.Call.LabelValue) !*LocalOperator {
        const state = self.data();
        const pending = try state.allocator.create(LocalOperatorImpl);
        pending.* = .{
            .owner = state,
            .item = .{
                .insertion = insertion,
                .kind = kind,
                .labels = try self.labelSpan(values),
            },
        };
        try state.pending_operators.append(state.allocator, pending);
        return @ptrCast(pending);
    }

    fn rawOperator(self: *Local, item: *LocalOperator) !kernel.Call.LocalOp {
        const state = self.data();
        const pending: *LocalOperatorImpl = @ptrCast(@alignCast(item));
        if (pending.owner != state) return error.InvalidLocalOperator;
        return pending.item;
    }

    fn addRaw(self: *Local, item: kernel.Call.LocalOp) !void {
        const state = self.data();
        if (state.finished) return error.LocalAlreadyFinished;
        try state.operators_list.append(state.allocator, item);
    }

    fn add(self: *Local, item: *LocalOperator) !void {
        try self.addRaw(try self.rawOperator(item));
    }

    fn isLocalOperatorToken(comptime Item: type) bool {
        return switch (@typeInfo(Item)) {
            .pointer => |ptr| ptr.child == LocalOperator,
            else => false,
        };
    }

    fn addItem(self: *Local, item: anytype) !void {
        if (comptime isLocalOperatorToken(@TypeOf(item))) {
            try self.add(item);
        } else {
            try self.addNormalOrdered(item);
        }
    }

    fn addNormalOrdered(self: *Local, items: anytype) !void {
        const state = self.data();
        const group = try normal_ordering.next(&state.next_normal_order_group);
        inline for (items) |item| {
            try self.addRaw(normal_ordering.tag(try self.rawOperator(item), group));
        }
    }

    /// ops freezes local operators; nested tuples are normal-ordered products.
    pub fn ops(self: *Local, items: anytype) !*OperatorList {
        inline for (items) |item| {
            try self.addItem(item);
        }
        return self.freeze();
    }

    fn freeze(self: *Local) !*OperatorList {
        const state = self.data();
        if (state.finished) return error.LocalAlreadyFinished;
        state.owned_operators = try state.operators_list.toOwnedSlice(state.allocator);
        state.owned_labels = try state.labels.toOwnedSlice(state.allocator);
        state.label_store = .{ .values = state.owned_labels };
        state.finished = true;
        return @ptrCast(state);
    }
};

/// wick exposes compact preset-author helpers for primitive Wick rule templates.
const wick = WickDsl;

const WickDsl = struct {
    /// Support tells the evaluator which insertion coordinate slots it reads.
    pub const Support = enum {
        holomorphic,
        antiholomorphic,
        bulk_pair,
        boundary,
    };

    /// Side selects the left or right operator in a Wick rule expression.
    pub const Side = enum { left, right };

    /// CoordinateSlot selects the coordinate component of a matched insertion.
    pub const CoordinateSlot = enum { position, holomorphic, antiholomorphic };

    /// CoordinateRef refers to one coordinate of one side of a Wick rule.
    pub const CoordinateRef = struct {
        side: Side,
        slot: CoordinateSlot,
    };

    /// LabelRef refers to one runtime label of one side of a Wick rule.
    pub const LabelRef = struct {
        side: Side,
        slot: u8,
    };

    /// ScalarFactor describes one non-coordinate scalar multiplier.
    pub const ScalarFactor = union(enum) {
        value: RuleScalar,
        label_bilinear_phase: struct { left: LabelRef, right: LabelRef, form: []const u8 },
        cocycle: struct { table: []const u8, left: LabelRef, right: LabelRef },
        spin_structure: []const u8,
    };

    /// TensorRef identifies tensor data coming from labels or selected config data.
    pub const TensorRef = union(enum) {
        label: LabelRef,
        config: ConfigRef,
    };

    /// TensorFactor describes one tensor multiplier in a Wick coefficient.
    pub const TensorFactor = union(enum) {
        none,
        metric: struct { left: LabelRef, right: LabelRef },
        momentum_index: struct { momentum: LabelRef, index: LabelRef },
        momentum_pair: struct { left: LabelRef, right: LabelRef },
        projector_metric: struct { projector: TensorRef, left: LabelRef, right: LabelRef },
        projector_momentum_index: struct { projector: TensorRef, momentum: LabelRef, index: LabelRef },
        projector_momentum_pair: struct { projector: TensorRef, left: LabelRef, right: LabelRef },
    };

    /// ActionFactor describes a non-multiplicative action produced by a Wick contraction.
    pub const ActionFactor = union(enum) {
        profile_derivative: struct { profile: LabelRef, index: LabelRef },
        projected_profile_derivative: struct { projector: TensorRef, profile: LabelRef, index: LabelRef },
    };

    /// CoordinateDifference is the coordinate difference read by a Wick kernel.
    pub const CoordinateDifference = struct {
        left: CoordinateRef,
        right: CoordinateRef,
    };

    /// DerivativeAction tells resolution how insertion derivative labels act on a coordinate factor.
    pub const DerivativeAction = struct {
        include_left: bool = false,
        include_right: bool = false,
    };

    /// CoordinateFactor describes one coordinate-dependent multiplier.
    pub const CoordinateFactor = union(enum) {
        difference_power: struct { coordinate: CoordinateDifference, exponent: i16, derivatives: DerivativeAction = .{} },
        logarithm: struct { coordinate: CoordinateDifference, derivatives: DerivativeAction = .{} },
        green_kernel: struct { name: []const u8, coordinate: CoordinateDifference, derivatives: DerivativeAction = .{} },
        green_exponential: CoordinateDifference,
    };

    /// Term is one product of scalar, coordinate, tensor, and action factors.
    pub const Term = struct {
        scalars: []const ScalarFactor,
        coordinates: []const CoordinateFactor,
        tensors: []const TensorFactor,
        actions: []const ActionFactor = &.{},
        residuals: []const Side = &.{},
    };

    /// Expr is a sum of Wick coefficient terms.
    pub const Expr = struct {
        terms: []const Term,
    };

    const PoleExpr = struct {
        scalar: ScalarFactor,
        numerator: TensorFactor,
        coordinate: CoordinateDifference,
        exponent: i16,
    };

    const GreenExponentialExpr = struct {
        scalar: ScalarFactor,
        momentum_pair: TensorFactor,
        coordinate: CoordinateDifference,
    };

    /// Pattern is one side of a primitive Wick rule.
    pub const Pattern = struct {
        kind: operators.OperatorKindId,
        support: Support,
    };

    /// Rule is one preset-authored primitive Wick rule.
    pub const Rule = struct {
        left: Pattern,
        right: Pattern,
        expr: Expr,
    };

    /// rule constructs one primitive Wick rule template.
    pub fn rule(left: Pattern, right: Pattern, expression: Expr) Rule {
        return .{ .left = left, .right = right, .expr = expression };
    }

    /// pattern constructs one Wick-rule side from a preset-owned kind id.
    pub fn pattern(comptime kind: operators.OperatorKindId, comptime support: Support) Pattern {
        return .{ .kind = kind, .support = support };
    }

    /// coord refers to one coordinate slot of one Wick-rule side.
    pub fn coord(side: Side, slot: CoordinateSlot) CoordinateRef {
        return .{ .side = side, .slot = slot };
    }

    /// label refers to one label slot of one Wick-rule side.
    pub fn label(side: Side, slot: u8) LabelRef {
        return .{ .side = side, .slot = slot };
    }

    /// difference constructs a coordinate difference.
    pub fn difference(left: CoordinateRef, right: CoordinateRef) CoordinateDifference {
        return .{ .left = left, .right = right };
    }

    /// scalar constructs a scalar factor from a rule scalar.
    pub fn scalar(comptime value: RuleScalar) ScalarFactor {
        return .{ .value = value };
    }

    /// term constructs one product term in a Wick expression.
    pub fn term(comptime scalar_factors: []const ScalarFactor, comptime coordinates: []const CoordinateFactor, comptime tensors: []const TensorFactor) Term {
        return .{ .scalars = scalar_factors, .coordinates = coordinates, .tensors = tensors };
    }

    /// termWithActions constructs one Wick term that also carries operator actions.
    pub fn termWithActions(comptime scalar_factors: []const ScalarFactor, comptime coordinates: []const CoordinateFactor, comptime tensors: []const TensorFactor, comptime actions: []const ActionFactor) Term {
        return .{ .scalars = scalar_factors, .coordinates = coordinates, .tensors = tensors, .actions = actions };
    }

    /// termWithResiduals constructs one Wick term with surviving input sides.
    pub fn termWithResiduals(comptime scalar_factors: []const ScalarFactor, comptime coordinates: []const CoordinateFactor, comptime tensors: []const TensorFactor, comptime actions: []const ActionFactor, comptime residuals: []const Side) Term {
        return .{ .scalars = scalar_factors, .coordinates = coordinates, .tensors = tensors, .actions = actions, .residuals = residuals };
    }

    /// expr constructs a Wick expression from one or more terms.
    pub fn expr(comptime terms: []const Term) Expr {
        return .{ .terms = terms };
    }

    /// profileDerivative constructs the action of a target derivative on a profile label.
    pub fn profileDerivative(comptime profile: LabelRef, comptime index: LabelRef) ActionFactor {
        return .{ .profile_derivative = .{ .profile = profile, .index = index } };
    }

    /// projectedProfileDerivative constructs a projected target derivative on a profile label.
    pub fn projectedProfileDerivative(comptime projector: TensorRef, comptime profile: LabelRef, comptime index: LabelRef) ActionFactor {
        return .{ .projected_profile_derivative = .{ .projector = projector, .profile = profile, .index = index } };
    }

    /// differencePower constructs a power of a coordinate difference.
    pub fn differencePower(comptime coordinate: CoordinateDifference, comptime exponent: i16) CoordinateFactor {
        return .{ .difference_power = .{ .coordinate = coordinate, .exponent = exponent } };
    }

    /// differentiatedPower applies matched insertion derivative labels to a coordinate power.
    pub fn differentiatedPower(comptime coordinate: CoordinateDifference, comptime exponent: i16, comptime derivatives: DerivativeAction) CoordinateFactor {
        return .{ .difference_power = .{ .coordinate = coordinate, .exponent = exponent, .derivatives = derivatives } };
    }

    /// logarithm constructs a logarithm of a coordinate difference.
    pub fn logarithm(comptime coordinate: CoordinateDifference) CoordinateFactor {
        return .{ .logarithm = .{ .coordinate = coordinate } };
    }

    /// differentiatedLogarithm applies matched insertion derivative labels to a logarithm.
    pub fn differentiatedLogarithm(comptime coordinate: CoordinateDifference, comptime derivatives: DerivativeAction) CoordinateFactor {
        return .{ .logarithm = .{ .coordinate = coordinate, .derivatives = derivatives } };
    }

    /// greenKernel constructs a named Green-kernel coordinate factor.
    pub fn greenKernel(comptime name: []const u8, comptime coordinate: CoordinateDifference) CoordinateFactor {
        return .{ .green_kernel = .{ .name = name, .coordinate = coordinate } };
    }

    /// differentiatedGreenKernel records derivative labels acting on a named Green kernel.
    pub fn differentiatedGreenKernel(comptime name: []const u8, comptime coordinate: CoordinateDifference, comptime derivatives: DerivativeAction) CoordinateFactor {
        return .{ .green_kernel = .{ .name = name, .coordinate = coordinate, .derivatives = derivatives } };
    }

    /// pole constructs a primitive pole coefficient.
    pub fn pole(comptime scalar_value: RuleScalar, comptime numerator: TensorFactor, comptime coordinate: CoordinateDifference, comptime exponent: i16) Expr {
        const shape = PoleExpr{
            .scalar = scalar(scalar_value),
            .numerator = numerator,
            .coordinate = coordinate,
            .exponent = exponent,
        };
        return expr(&.{term(&.{shape.scalar}, &.{differencePower(shape.coordinate, shape.exponent)}, &.{shape.numerator})});
    }

    /// differentiatedPole constructs a pole acted on by matched insertion derivatives.
    pub fn differentiatedPole(comptime scalar_value: RuleScalar, comptime numerator: TensorFactor, comptime coordinate: CoordinateDifference, comptime exponent: i16, comptime derivatives: DerivativeAction) Expr {
        const scalar_factor = scalar(scalar_value);
        return expr(&.{term(&.{scalar_factor}, &.{differentiatedPower(coordinate, exponent, derivatives)}, &.{numerator})});
    }

    /// differentiatedActionPole constructs a differentiated pole carrying profile or custom actions.
    pub fn differentiatedActionPole(comptime scalar_value: RuleScalar, comptime numerator: TensorFactor, comptime coordinate: CoordinateDifference, comptime exponent: i16, comptime derivatives: DerivativeAction, comptime actions: []const ActionFactor) Expr {
        const scalar_factor = scalar(scalar_value);
        return expr(&.{termWithActions(&.{scalar_factor}, &.{differentiatedPower(coordinate, exponent, derivatives)}, &.{numerator}, actions)});
    }

    /// differentiatedPoleWithResiduals constructs a differentiated pole with surviving sides.
    pub fn differentiatedPoleWithResiduals(comptime scalar_value: RuleScalar, comptime numerator: TensorFactor, comptime coordinate: CoordinateDifference, comptime exponent: i16, comptime derivatives: DerivativeAction, comptime residuals: []const Side) Expr {
        const scalar_factor = scalar(scalar_value);
        return expr(&.{termWithResiduals(&.{scalar_factor}, &.{differentiatedPower(coordinate, exponent, derivatives)}, &.{numerator}, &.{}, residuals)});
    }

    /// differentiatedActionPoleWithResiduals constructs an action pole with surviving sides.
    pub fn differentiatedActionPoleWithResiduals(comptime scalar_value: RuleScalar, comptime numerator: TensorFactor, comptime coordinate: CoordinateDifference, comptime exponent: i16, comptime derivatives: DerivativeAction, comptime actions: []const ActionFactor, comptime residuals: []const Side) Expr {
        const scalar_factor = scalar(scalar_value);
        return expr(&.{termWithResiduals(&.{scalar_factor}, &.{differentiatedPower(coordinate, exponent, derivatives)}, &.{numerator}, actions, residuals)});
    }

    /// greenExponential constructs a plane-wave Green-kernel factor.
    pub fn greenExponential(comptime scalar_value: RuleScalar, comptime momentum_pair: TensorFactor, comptime coordinate: CoordinateDifference) Expr {
        const shape = GreenExponentialExpr{
            .scalar = scalar(scalar_value),
            .momentum_pair = momentum_pair,
            .coordinate = coordinate,
        };
        return expr(&.{term(&.{shape.scalar}, &.{.{ .green_exponential = shape.coordinate }}, &.{shape.momentum_pair})});
    }

    /// greenExponentialWithResiduals constructs a Green factor with surviving sides.
    pub fn greenExponentialWithResiduals(comptime scalar_value: RuleScalar, comptime momentum_pair: TensorFactor, comptime coordinate: CoordinateDifference, comptime residuals: []const Side) Expr {
        const shape = GreenExponentialExpr{
            .scalar = scalar(scalar_value),
            .momentum_pair = momentum_pair,
            .coordinate = coordinate,
        };
        return expr(&.{termWithResiduals(&.{shape.scalar}, &.{.{ .green_exponential = shape.coordinate }}, &.{shape.momentum_pair}, &.{}, residuals)});
    }
};

/// Spec stores internal declarative metadata before lowering to runtime tables.
const Spec = struct {
    /// LabelKind classifies one operator label slot.
    pub const LabelKind = enum {
        index,
        momentum,
        profile,
    };

    /// InsertionShape records the runtime insertion packer required by an operator.
    pub const InsertionShape = enum {
        single,
        pair,
    };

    /// Statistics records the exchange parity of an operator family.
    pub const Statistics = enum {
        bosonic,
        fermionic,
    };

    /// Operator declares one local-field family before lowering.
    pub const Operator = struct {
        name: []const u8,
        kind: operators.OperatorKindId,
        support: wick.Support,
        insertion: InsertionShape,
        labels: []const LabelKind = &.{},
        statistics: Statistics,
        zero_mode_consumable: bool = false,
    };

    /// CoordinateKernel names the coordinate-factor family required by a Wick rule.
    pub const CoordinateKernel = enum {
        rational_pole,
        rational_green_exponential,
        elliptic_green,
        elliptic_green_exponential,
        elliptic_prime_form,
        elliptic_prime_form_log_derivative,
    };

    /// WickRule records the abstract endpoints, primitive terms, and coordinate kernels.
    pub const WickRule = struct {
        left: operators.OperatorKindId,
        right: operators.OperatorKindId,
        term_count: usize = 1,
        expr: ?wick.Expr = null,
        coordinate_kernels: []const CoordinateKernel = &.{},
    };

    /// ZeroModeKind identifies implemented and draft zero-mode spec families.
    pub const ZeroModeKind = enum {
        runtime,
        torus_free_boson_constant,
        torus_bc_moduli,
        torus_eta_xi_zero_mode,
    };

    /// ZeroModeRule records one residual base-case consumer family.
    pub const ZeroModeRule = struct {
        sector: zero_mode.Sector,
        kind: ZeroModeKind = .runtime,
        expr: ?zero_mode.Expr = null,
        consumes: []const operators.OperatorKindId = &.{},
    };

    /// SurfaceKind names the topology class described by a theory spec.
    pub const SurfaceKind = enum {
        sphere,
        disk,
        torus,
    };

    /// CoordinateModel selects the coordinate kernel family for a surface.
    pub const CoordinateModel = enum {
        rational,
        elliptic,
    };

    /// SurfaceSource records where a surface convention is fixed.
    pub const SurfaceSource = enum {
        preset,
        stringbook,
    };

    /// Surface records topology and modular data before runtime lowering.
    pub const Surface = struct {
        kind: SurfaceKind = .sphere,
        coordinate_model: CoordinateModel = .rational,
        modular_parameters: []const []const u8 = &.{},
        source: SurfaceSource = .preset,
    };

    /// Theory groups the declarative metadata for one preset surface.
    pub const Theory = struct {
        surface: Surface = .{},
        operators: []const Operator,
        wick_rules: []const WickRule,
        zero_modes: []const ZeroModeRule,
    };

    /// zeroModeRule lowers one declarative zero-mode spec into the runtime rule.
    pub fn zeroModeRule(comptime rule: ZeroModeRule) zero_mode.Rule {
        const expr = rule.expr orelse @compileError("draft zero-mode spec cannot be lowered to runtime rules");
        return zero_mode.rule(rule.sector, expr);
    }

    /// zeroModeRules lowers declarative zero-mode specs into runtime rules.
    pub fn zeroModeRules(comptime rules: []const ZeroModeRule) [rules.len]zero_mode.Rule {
        var storage: [rules.len]zero_mode.Rule = undefined;
        inline for (rules, 0..) |rule, index| {
            storage[index] = zeroModeRule(rule);
        }
        return storage;
    }

    /// zeroModeConsumeKindCount returns the number of operator-kind families accepted by a zero-mode spec.
    pub fn zeroModeConsumeKindCount(comptime rule: ZeroModeRule) usize {
        const expr = rule.expr orelse return rule.consumes.len;
        return switch (expr) {
            .bc_top_form => |payload| payload.c_kind_ids.len,
            .free_boson_constant_mode => |payload| payload.exp_kind_ids.len + payload.profile_kind_ids.len,
            .eta_xi_zero_mode => |payload| payload.xi_kind_ids.len,
            .constant_fermion => |payload| payload.fermion_kind_ids.len,
            .top_form_fermion => |payload| payload.field_kind_ids.len,
            .boson_momentum_conservation => |payload| payload.exp_kind_ids.len + payload.profile_kind_ids.len,
        };
    }

    /// wickCoordinateKernelCount counts Wick rules that require one coordinate kernel family.
    pub fn wickCoordinateKernelCount(comptime rules: []const WickRule, comptime expected_kernel: CoordinateKernel) usize {
        comptime var count: usize = 0;
        inline for (rules) |rule| {
            inline for (rule.coordinate_kernels) |candidate| {
                if (candidate == expected_kernel) count += 1;
            }
        }
        return count;
    }

    fn operatorSupport(comptime operator_specs: []const Operator, comptime kind_id: operators.OperatorKindId) wick.Support {
        inline for (operator_specs) |operator| {
            if (operator.kind == kind_id) return operator.support;
        }
        @compileError("missing operator spec for Wick rule endpoint");
    }

    /// wickRule lowers one declarative Wick spec into the runtime rule table.
    pub fn wickRule(comptime rule: WickRule, comptime operator_specs: []const Operator) wick.Rule {
        const expression = rule.expr orelse @compileError("draft Wick spec cannot be lowered to runtime rules");
        return wick.rule(
            wick.pattern(rule.left, operatorSupport(operator_specs, rule.left)),
            wick.pattern(rule.right, operatorSupport(operator_specs, rule.right)),
            expression,
        );
    }

    /// wickRules lowers declarative Wick specs into the runtime rule table.
    pub fn wickRules(comptime rules: []const WickRule, comptime operator_specs: []const Operator) [rules.len]wick.Rule {
        var storage: [rules.len]wick.Rule = undefined;
        inline for (rules, 0..) |rule, index| {
            storage[index] = wickRule(rule, operator_specs);
        }
        return storage;
    }

    /// fermionKindCount counts operators that contribute exchange signs.
    pub fn fermionKindCount(comptime operator_specs: []const Operator) usize {
        comptime var count: usize = 0;
        inline for (operator_specs) |operator| {
            if (operator.statistics == .fermionic) count += 1;
        }
        return count;
    }

    /// fermionKinds lowers operator statistics into runtime fermion kind ids.
    pub fn fermionKinds(comptime operator_specs: []const Operator) [fermionKindCount(operator_specs)]operators.OperatorKindId {
        var storage: [fermionKindCount(operator_specs)]operators.OperatorKindId = undefined;
        comptime var index: usize = 0;
        inline for (operator_specs) |operator| {
            if (operator.statistics == .fermionic) {
                storage[index] = operator.kind;
                index += 1;
            }
        }
        return storage;
    }
};

fn coordVariable(coord: Handle.Coord) u32 {
    return rawToken(coord);
}

fn singleInsertion(z: Handle.Coord, derivatives: u8) operators.OperatorInsertion {
    return .{ .single = .{
        .position = coordVariable(z),
        .derivatives = derivatives,
    } };
}

fn pairInsertion(z: Handle.Coord, zbar: Handle.Coord) operators.OperatorInsertion {
    return .{ .pair = .{
        .holomorphic_position = coordVariable(z),
        .antiholomorphic_position = coordVariable(zbar),
        .holomorphic_derivatives = 0,
        .antiholomorphic_derivatives = 0,
    } };
}

fn labelTupleCount(comptime Labels: type) comptime_int {
    const info = @typeInfo(Labels);
    if (info != .@"struct" or !info.@"struct".is_tuple) @compileError("operator labels must be passed as a tuple");
    return info.@"struct".fields.len;
}

fn fillSymbolLabels(comptime count: usize, out: *[count]kernel.Call.LabelValue, labels: anytype) void {
    inline for (0..count) |index| {
        out[index] = Local.symbol(labels[index]);
    }
}

fn buildKindOperator(local: *Local, kind_id: operators.OperatorKindId, insertion: operators.OperatorInsertion, labels: anytype) !*LocalOperator {
    const count = comptime labelTupleCount(@TypeOf(labels));
    var values: [count]kernel.Call.LabelValue = undefined;
    fillSymbolLabels(count, &values, labels);
    return local.op(kind_id, insertion, values[0..]);
}

fn assertOperatorShape(comptime operator: Spec.Operator, comptime insertion: Spec.InsertionShape, comptime label_count: usize) void {
    if (operator.insertion != insertion) @compileError("operator builder insertion shape does not match spec");
    if (operator.labels.len != label_count) @compileError("operator builder label count does not match spec");
}

fn boundaryCoord(y: Handle.BoundaryCoord) Handle.Coord {
    return token(Handle.Coord, rawToken(y));
}

fn buildSingleOperator(local: *Local, comptime operator: Spec.Operator, z: Handle.Coord, derivatives: u8, labels: anytype) !*LocalOperator {
    comptime assertOperatorShape(operator, .single, labelTupleCount(@TypeOf(labels)));
    return buildKindOperator(local, operator.kind, singleInsertion(z, derivatives), labels);
}

fn buildPairOperator(local: *Local, comptime operator: Spec.Operator, z: Handle.Coord, zbar: Handle.Coord, labels: anytype) !*LocalOperator {
    comptime assertOperatorShape(operator, .pair, labelTupleCount(@TypeOf(labels)));
    return buildKindOperator(local, operator.kind, pairInsertion(z, zbar), labels);
}

fn localBuilder(local: anytype) *Local {
    const Input = @TypeOf(local);
    return switch (@typeInfo(Input)) {
        .pointer => |ptr| if (ptr.child == Local)
            local
        else if (ptr.child == *Local)
            local.*
        else
            @compileError("operator builders require a local builder"),
        else => @compileError("operator builders require a local builder"),
    };
}

/// operatorBuilder generates insertion and label packing from one operator schema.
fn operatorBuilder(comptime operator: Spec.Operator) type {
    return struct {
        /// single builds a single-coordinate local operator from this schema.
        pub fn single(local: anytype, z: Handle.Coord, derivatives: u8, labels: anytype) !*LocalOperator {
            return buildSingleOperator(localBuilder(local), operator, z, derivatives, labels);
        }

        /// boundarySingle builds a boundary single-coordinate local operator from this schema.
        pub fn boundarySingle(local: anytype, y: Handle.BoundaryCoord, derivatives: u8, labels: anytype) !*LocalOperator {
            return buildSingleOperator(localBuilder(local), operator, boundaryCoord(y), derivatives, labels);
        }

        /// pair builds a bulk-pair local operator from this schema.
        pub fn pair(local: anytype, z: Handle.Coord, zbar: Handle.Coord, labels: anytype) !*LocalOperator {
            return buildPairOperator(localBuilder(local), operator, z, zbar, labels);
        }
    };
}

/// zero_mode exposes compact preset-author helpers for zero-mode rules.
const zero_mode = ZeroModeDsl;

const ZeroModeDsl = struct {
    /// Sector names a preset-owned zero-mode sector.
    pub const Sector = u32;

    /// BcSupport selects the finite c-zero-mode basis used by the bc evaluator.
    pub const BcSupport = enum {
        sphere_holomorphic,
        sphere_antiholomorphic,
        disk_doubled,
    };

    /// BcTopForm declares one top-form ghost zero-mode saturation rule.
    pub const BcTopForm = struct {
        support: BcSupport,
        c_kind_ids: []const operators.OperatorKindId,
        normalization: RuleScalar = .one,
    };

    /// EtaXiSupport selects the chiral xi constant mode saturated by a surface.
    pub const EtaXiSupport = enum {
        sphere_holomorphic,
        sphere_antiholomorphic,
        torus_holomorphic,
        torus_antiholomorphic,
    };

    /// EtaXiZeroMode declares one xi constant-mode saturation rule.
    pub const EtaXiZeroMode = struct {
        support: EtaXiSupport,
        xi_kind_ids: []const operators.OperatorKindId,
        normalization: RuleScalar = .one,
    };

    /// ConstantFermion declares one generic constant fermion saturation rule.
    pub const ConstantFermion = struct {
        support: EtaXiSupport,
        fermion_kind_ids: []const operators.OperatorKindId,
        normalization: RuleScalar = .one,
    };

    /// TopFormFermion declares one generic top-form fermion saturation rule.
    pub const TopFormFermion = struct {
        support: BcSupport,
        field_kind_ids: []const operators.OperatorKindId,
        normalization: RuleScalar = .one,
    };

    /// RankSource records where a power of 2pi gets its exponent.
    pub const RankSource = union(enum) {
        none,
        literal: u16,
        target_dimension: ConfigRef,
        projector_rank: ConfigRef,
    };

    /// Normalization records the CFT normalization attached to a zero-mode rule.
    pub const Normalization = struct {
        scalar: RuleScalar = .one,
        two_pi_power: RankSource = .none,
    };

    /// FreeBosonConstantMode declares the free-boson constant-mode base case.
    pub const FreeBosonConstantMode = struct {
        integration_projector: ?ConfigRef = null,
        fixed_projector: ?ConfigRef = null,
        fixed_position: ?ConfigRef = null,
        exp_kind_ids: []const operators.OperatorKindId,
        profile_kind_ids: []const operators.OperatorKindId,
        normalization: Normalization = .{},
    };

    /// Expr selects the zero-mode evaluator and payload.
    pub const Expr = union(enum) {
        bc_top_form: BcTopForm,
        free_boson_constant_mode: FreeBosonConstantMode,
        eta_xi_zero_mode: EtaXiZeroMode,
        constant_fermion: ConstantFermion,
        top_form_fermion: TopFormFermion,
        boson_momentum_conservation: FreeBosonConstantMode,
    };

    /// Rule is one preset-authored zero-mode rule.
    pub const Rule = struct {
        sector: Sector,
        expr: Expr,
    };

    /// rule constructs a zero-mode rule.
    pub fn rule(sector: Sector, expr: Expr) Rule {
        return .{ .sector = sector, .expr = expr };
    }
};

const PairLookupEntry = struct {
    key: u64,
    rule_index: u32,
    reversed: bool,
};

const BranchBudget = enum {
    standard,
};

const BranchLimits = struct {
    max_operators: usize,
    max_zero_mode_residuals: usize,
    max_zero_mode_items: usize,
    max_terms: usize,
    max_scalars: usize,
    max_coordinates: usize,
    max_tensors: usize,
    max_actions: usize,
    max_residuals: usize,
    max_cached_terms: usize,
    max_cached_scalars: usize,
    max_cached_coordinates: usize,
    max_cached_tensors: usize,
    max_cached_actions: usize,
    max_cached_residuals: usize,
};

const CorrelatorConfigInput = struct {
    wick_rules: []const wick.Rule,
    zero_modes: []const zero_mode.Rule,
    config_entries: []const ConfigEntry = &.{},
    fermion_kinds: []const operators.OperatorKindId = &.{},
    branch_budget: BranchBudget = .standard,
};

const CorrelatorConfigData = struct {
    wick_rules: []const wick.Rule,
    pair_lookup: []const PairLookupEntry,
    zero_modes: []const zero_mode.Rule,
    config_entries: []const ConfigEntry,
    fermion_kinds: []const operators.OperatorKindId,
};

/// correlatorConfig creates an opaque public handle for lowered correlator data.
fn correlatorConfig(comptime input: CorrelatorConfigInput) type {
    return struct {
        const branch_limits = branchLimits(input);
        const pair_lookup_storage = pairLookupStorage(input.wick_rules);
        const impl = CorrelatorConfigData{
            .wick_rules = input.wick_rules,
            .pair_lookup = &pair_lookup_storage,
            .zero_modes = input.zero_modes,
            .config_entries = input.config_entries,
            .fermion_kinds = input.fermion_kinds,
        };
    };
}

fn configData(config_ptr: anytype) *const CorrelatorConfigData {
    const Ptr = @TypeOf(config_ptr);
    const ptr_info = @typeInfo(Ptr);
    if (ptr_info != .pointer) @compileError("correlator config must be passed by pointer");
    const Config = ptr_info.pointer.child;
    if (!@hasDecl(Config, "impl")) @compileError("invalid correlator config handle");
    return &Config.impl;
}

const ConfigValue = union(enum) {
    tensor_projector: Handle.TensorProjector,
    target_point: Handle.TargetPoint,
    target_dimension: u16,
    boundary_stack: Handle.BoundaryStack,
};

const ConfigEntry = struct {
    id: ConfigRef,
    value: ConfigValue,
};

/// config exposes typed constructors for private config payload entries.
const ConfigDsl = struct {
    /// tensorProjector binds a tensor-projector handle to a config reference.
    pub fn tensorProjector(id: ConfigRef, value: Handle.TensorProjector) ConfigEntry {
        return .{ .id = id, .value = .{ .tensor_projector = value } };
    }

    /// targetPoint binds a target-space point handle to a config reference.
    pub fn targetPoint(id: ConfigRef, value: Handle.TargetPoint) ConfigEntry {
        return .{ .id = id, .value = .{ .target_point = value } };
    }

    /// targetDimension binds a target-space dimension to a config reference.
    pub fn targetDimension(id: ConfigRef, value: u16) ConfigEntry {
        return .{ .id = id, .value = .{ .target_dimension = value } };
    }

    /// boundaryStack binds Chan-Paton boundary-stack data to a config reference.
    pub fn boundaryStack(id: ConfigRef, value: Handle.BoundaryStack) ConfigEntry {
        return .{ .id = id, .value = .{ .boundary_stack = value } };
    }
};

/// configEntries packs typed config entries without exposing their carrier type.
fn configEntries(comptime entries: anytype) [@typeInfo(@TypeOf(entries)).@"struct".fields.len]ConfigEntry {
    var storage: [@typeInfo(@TypeOf(entries)).@"struct".fields.len]ConfigEntry = undefined;
    inline for (entries, 0..) |entry, index| {
        storage[index] = entry;
    }
    return storage;
}

const BoundaryExtensionInput = struct {
    op: type,
    wick_rules: []const wick.Rule,
    zero_modes: []const zero_mode.Rule,
    config_entries: []const ConfigEntry = &.{},
    fermion_kinds: []const operators.OperatorKindId = &.{},
};

const BoundaryExtensionData = struct {
    wick_rules: []const wick.Rule,
    zero_modes: []const zero_mode.Rule,
    config_entries: []const ConfigEntry,
    fermion_kinds: []const operators.OperatorKindId,
};

const LoweredSlice = enum {
    wick_rules,
    zero_modes,
    config_entries,
    fermion_kinds,
};

fn correlatorSliceCount(config_ptr: anytype, comptime slice: LoweredSlice) usize {
    const data = configData(config_ptr);
    return switch (slice) {
        .wick_rules => data.wick_rules.len,
        .zero_modes => data.zero_modes.len,
        .config_entries => data.config_entries.len,
        .fermion_kinds => data.fermion_kinds.len,
    };
}

fn appendCorrelatorSlice(config_ptr: anytype, comptime slice: LoweredSlice, storage: anytype, index: *usize) void {
    const data = configData(config_ptr);
    switch (slice) {
        .wick_rules => for (data.wick_rules) |item| {
            storage[index.*] = item;
            index.* += 1;
        },
        .zero_modes => for (data.zero_modes) |item| {
            storage[index.*] = item;
            index.* += 1;
        },
        .config_entries => for (data.config_entries) |item| {
            storage[index.*] = item;
            index.* += 1;
        },
        .fermion_kinds => for (data.fermion_kinds) |item| {
            storage[index.*] = item;
            index.* += 1;
        },
    }
}

/// BoundaryExtension creates an opaque public handle for boundary preset data.
fn BoundaryExtension(comptime input: BoundaryExtensionInput) type {
    return struct {
        /// op exposes boundary-local operator builders for this extension.
        pub const op = input.op;
        const impl = BoundaryExtensionData{
            .wick_rules = input.wick_rules,
            .zero_modes = input.zero_modes,
            .config_entries = input.config_entries,
            .fermion_kinds = input.fermion_kinds,
        };
    };
}

fn boundaryExtensionData(comptime extension: anytype) BoundaryExtensionData {
    const Extension = @TypeOf(extension);
    if (!@hasDecl(Extension, "impl")) @compileError("invalid boundary extension handle");
    return Extension.impl;
}

fn boundaryExtensionSliceCount(comptime extension: anytype, comptime slice: LoweredSlice) usize {
    const data = boundaryExtensionData(extension);
    return switch (slice) {
        .wick_rules => data.wick_rules.len,
        .zero_modes => data.zero_modes.len,
        .config_entries => data.config_entries.len,
        .fermion_kinds => data.fermion_kinds.len,
    };
}

fn appendBoundaryExtensionSlice(comptime extension: anytype, comptime slice: LoweredSlice, storage: anytype, index: *usize) void {
    const data = boundaryExtensionData(extension);
    switch (slice) {
        .wick_rules => for (data.wick_rules) |item| {
            storage[index.*] = item;
            index.* += 1;
        },
        .zero_modes => for (data.zero_modes) |item| {
            storage[index.*] = item;
            index.* += 1;
        },
        .config_entries => for (data.config_entries) |item| {
            storage[index.*] = item;
            index.* += 1;
        },
        .fermion_kinds => for (data.fermion_kinds) |item| {
            storage[index.*] = item;
            index.* += 1;
        },
    }
}

fn factorHasSphereConfig(comptime Factor: type) bool {
    return @hasDecl(Factor, "config") and @hasDecl(Factor.config, "sphere");
}

fn sphereConfigSliceCount(comptime factors: anytype, comptime slice: LoweredSlice) usize {
    var count: usize = 0;
    inline for (factors) |Factor| {
        if (factorHasSphereConfig(Factor)) count += correlatorSliceCount(&Factor.config.sphere, slice);
    }
    return count;
}

fn appendSphereConfigSlice(comptime factors: anytype, comptime slice: LoweredSlice, storage: anytype) void {
    var index: usize = 0;
    inline for (factors) |Factor| {
        if (factorHasSphereConfig(Factor)) {
            appendCorrelatorSlice(&Factor.config.sphere, slice, storage, &index);
        }
    }
}

fn mergedSphereWickStorage(comptime factors: anytype) [sphereConfigSliceCount(factors, .wick_rules)]wick.Rule {
    var storage: [sphereConfigSliceCount(factors, .wick_rules)]wick.Rule = undefined;
    appendSphereConfigSlice(factors, .wick_rules, storage[0..]);
    return storage;
}

fn mergedSphereZeroStorage(comptime factors: anytype) [sphereConfigSliceCount(factors, .zero_modes)]zero_mode.Rule {
    var storage: [sphereConfigSliceCount(factors, .zero_modes)]zero_mode.Rule = undefined;
    appendSphereConfigSlice(factors, .zero_modes, storage[0..]);
    return storage;
}

fn mergedSphereConfigStorage(comptime factors: anytype) [sphereConfigSliceCount(factors, .config_entries)]ConfigEntry {
    var storage: [sphereConfigSliceCount(factors, .config_entries)]ConfigEntry = undefined;
    appendSphereConfigSlice(factors, .config_entries, storage[0..]);
    return storage;
}

fn mergedSphereFermionStorage(comptime factors: anytype) [sphereConfigSliceCount(factors, .fermion_kinds)]operators.OperatorKindId {
    var storage: [sphereConfigSliceCount(factors, .fermion_kinds)]operators.OperatorKindId = undefined;
    appendSphereConfigSlice(factors, .fermion_kinds, storage[0..]);
    return storage;
}

/// mergeSphereConfigs builds one opaque sphere config from independent factors.
fn mergeSphereConfigs(comptime factors: anytype) type {
    return struct {
        const wick_storage = mergedSphereWickStorage(factors);
        const zero_storage = mergedSphereZeroStorage(factors);
        const config_storage = mergedSphereConfigStorage(factors);
        const fermion_storage = mergedSphereFermionStorage(factors);

        /// config is the merged sphere correlator config handle.
        pub const config = correlatorConfig(.{
            .wick_rules = &wick_storage,
            .zero_modes = &zero_storage,
            .config_entries = &config_storage,
            .fermion_kinds = &fermion_storage,
        }){};
    };
}

fn boundaryExtensionSliceTotal(comptime extensions: anytype, comptime slice: LoweredSlice) usize {
    var count: usize = 0;
    inline for (extensions) |extension| {
        count += boundaryExtensionSliceCount(extension, slice);
    }
    return count;
}

fn boundaryConfigSliceCount(comptime Bulk: type, comptime extensions: anytype, comptime slice: LoweredSlice) usize {
    var count: usize = 0;
    if (factorHasSphereConfig(Bulk)) count += correlatorSliceCount(&Bulk.config.sphere, slice);
    inline for (extensions) |extension| {
        count += boundaryExtensionSliceCount(extension, slice);
    }
    return count;
}

fn appendBoundaryExtensionSlices(comptime extensions: anytype, comptime slice: LoweredSlice, storage: anytype) void {
    var index: usize = 0;
    inline for (extensions) |extension| {
        appendBoundaryExtensionSlice(extension, slice, storage, &index);
    }
}

fn appendBoundaryConfigSlices(comptime Bulk: type, comptime extensions: anytype, comptime slice: LoweredSlice, storage: anytype) void {
    var index: usize = 0;
    if (factorHasSphereConfig(Bulk)) {
        appendCorrelatorSlice(&Bulk.config.sphere, slice, storage, &index);
    }
    inline for (extensions) |extension| {
        appendBoundaryExtensionSlice(extension, slice, storage, &index);
    }
}

fn mergedBoundaryWickStorage(comptime extensions: anytype) [boundaryExtensionSliceTotal(extensions, .wick_rules)]wick.Rule {
    var storage: [boundaryExtensionSliceTotal(extensions, .wick_rules)]wick.Rule = undefined;
    appendBoundaryExtensionSlices(extensions, .wick_rules, storage[0..]);
    return storage;
}

fn mergedBoundaryZeroStorage(comptime extensions: anytype) [boundaryExtensionSliceTotal(extensions, .zero_modes)]zero_mode.Rule {
    var storage: [boundaryExtensionSliceTotal(extensions, .zero_modes)]zero_mode.Rule = undefined;
    appendBoundaryExtensionSlices(extensions, .zero_modes, storage[0..]);
    return storage;
}

fn mergedBoundaryConfigStorage(comptime Bulk: type, comptime extensions: anytype) [boundaryConfigSliceCount(Bulk, extensions, .config_entries)]ConfigEntry {
    var storage: [boundaryConfigSliceCount(Bulk, extensions, .config_entries)]ConfigEntry = undefined;
    appendBoundaryConfigSlices(Bulk, extensions, .config_entries, storage[0..]);
    return storage;
}

fn mergedBoundaryFermionStorage(comptime Bulk: type, comptime extensions: anytype) [boundaryConfigSliceCount(Bulk, extensions, .fermion_kinds)]operators.OperatorKindId {
    var storage: [boundaryConfigSliceCount(Bulk, extensions, .fermion_kinds)]operators.OperatorKindId = undefined;
    appendBoundaryConfigSlices(Bulk, extensions, .fermion_kinds, storage[0..]);
    return storage;
}

/// mergeBoundaryConfig builds one opaque disk config from bulk data and extensions.
fn mergeBoundaryConfig(comptime Bulk: type, comptime extensions: anytype) type {
    return struct {
        const wick_storage = mergedBoundaryWickStorage(extensions);
        const zero_storage = mergedBoundaryZeroStorage(extensions);
        const config_storage = mergedBoundaryConfigStorage(Bulk, extensions);
        const fermion_storage = mergedBoundaryFermionStorage(Bulk, extensions);

        /// config is the merged disk correlator config handle.
        pub const config = correlatorConfig(.{
            .wick_rules = &wick_storage,
            .zero_modes = &zero_storage,
            .config_entries = &config_storage,
            .fermion_kinds = &fermion_storage,
        }){};
    };
}

const DeclareSpec = Spec;
const DeclareWick = wick;
const DeclareZeroMode = zero_mode;
const DeclareScalars = scalars;
const DeclareConfig = ConfigDsl;
const declareConfigRef = configRef;
const declareFamilyKind = familyKind;
const declareSectorId = sectorId;
const declareOperatorBuilder = operatorBuilder;
const declareCorrelatorConfig = correlatorConfig;
const declareBoundaryExtension = BoundaryExtension;
const declareConfigEntries = configEntries;
const declareMergeSphereConfigs = mergeSphereConfigs;
const declareMergeBoundaryConfig = mergeBoundaryConfig;

/// declare exposes preset declaration lowering without leaking individual internals.
pub const declare = struct {
    /// Spec stores declarative metadata before lowering to runtime tables.
    pub const Spec = DeclareSpec;
    /// wick exposes compact preset-author helpers for Wick rules.
    pub const wick = DeclareWick;
    /// zero_mode exposes compact preset-author helpers for zero-mode rules.
    pub const zero_mode = DeclareZeroMode;
    /// scalars exposes exact scalar helpers for preset rule coefficients.
    pub const scalars = DeclareScalars;
    /// config exposes typed constructors for private config payload entries.
    pub const config = DeclareConfig;

    /// configRef derives a compact config id from a namespace-local name.
    pub const configRef = declareConfigRef;
    /// familyKind derives a compact operator kind id from a preset family tag.
    pub const familyKind = declareFamilyKind;
    /// sectorId derives a compact zero-mode sector id from a preset sector tag.
    pub const sectorId = declareSectorId;
    /// operatorBuilder generates insertion and label packing from one operator schema.
    pub const operatorBuilder = declareOperatorBuilder;
    /// correlatorConfig creates an opaque public handle for lowered correlator data.
    pub const correlatorConfig = declareCorrelatorConfig;
    /// BoundaryExtension creates an opaque public handle for boundary preset data.
    pub const BoundaryExtension = declareBoundaryExtension;
    /// configEntries packs typed config entries without exposing their carrier type.
    pub const configEntries = declareConfigEntries;
    /// mergeSphereConfigs builds one opaque sphere config from independent factors.
    pub const mergeSphereConfigs = declareMergeSphereConfigs;
    /// mergeBoundaryConfig builds one opaque disk config from bulk data and extensions.
    pub const mergeBoundaryConfig = declareMergeBoundaryConfig;
};

fn wickRuleKey(left_kind: operators.OperatorKindId, right_kind: operators.OperatorKindId) u64 {
    return (@as(u64, left_kind) << 32) | @as(u64, right_kind);
}

fn pairLookupEntryCount(comptime rules: []const wick.Rule) usize {
    var count: usize = 0;
    for (rules) |rule| {
        count += 1;
        if (rule.left.kind != rule.right.kind) count += 1;
    }
    return count;
}

fn sortPairLookup(entries: []PairLookupEntry) void {
    var index: usize = 1;
    while (index < entries.len) : (index += 1) {
        const value = entries[index];
        var hole = index;
        while (hole > 0 and entries[hole - 1].key > value.key) : (hole -= 1) {
            entries[hole] = entries[hole - 1];
        }
        entries[hole] = value;
    }
}

fn pairLookupStorage(comptime rules: []const wick.Rule) [pairLookupEntryCount(rules)]PairLookupEntry {
    var entries: [pairLookupEntryCount(rules)]PairLookupEntry = undefined;
    var entry_index: usize = 0;

    for (rules, 0..) |rule, rule_index| {
        if (rule_index > std.math.maxInt(u32)) @compileError("too many Wick rules for compact rule index");
        entries[entry_index] = .{
            .key = wickRuleKey(rule.left.kind, rule.right.kind),
            .rule_index = @intCast(rule_index),
            .reversed = false,
        };
        entry_index += 1;

        if (rule.left.kind != rule.right.kind) {
            entries[entry_index] = .{
                .key = wickRuleKey(rule.right.kind, rule.left.kind),
                .rule_index = @intCast(rule_index),
                .reversed = true,
            };
            entry_index += 1;
        }
    }

    sortPairLookup(entries[0..]);
    return entries;
}

const Correlator = struct {
    /// WickPair is one oriented primitive Wick contraction between two concrete local operators.
    const WickPair = struct {
        rule: *const wick.Rule,
        config: *const CorrelatorConfigData,
        left: kernel.Call.LocalOp,
        right: kernel.Call.LocalOp,
        labels: *const kernel.Call.LabelStore,
        reversed: bool,

        fn sideOp(self: WickPair, side: wick.Side) kernel.Call.LocalOp {
            return switch (side) {
                .left => if (self.reversed) self.right else self.left,
                .right => if (self.reversed) self.left else self.right,
            };
        }

        fn coordinate(self: WickPair, coordinate_ref: wick.CoordinateRef) ?coefficient.Variable {
            const op = self.sideOp(coordinate_ref.side);
            return switch (op.insertion) {
                .single => |single| switch (coordinate_ref.slot) {
                    .position, .holomorphic => single.position,
                    .antiholomorphic => null,
                },
                .pair => |pair| switch (coordinate_ref.slot) {
                    .position, .holomorphic => pair.holomorphic_position,
                    .antiholomorphic => pair.antiholomorphic_position,
                },
            };
        }

        fn derivativeCount(self: WickPair, coordinate_ref: wick.CoordinateRef) ?u8 {
            const op = self.sideOp(coordinate_ref.side);
            return switch (op.insertion) {
                .single => |single| switch (coordinate_ref.slot) {
                    .position, .holomorphic => single.derivatives,
                    .antiholomorphic => null,
                },
                .pair => |pair| switch (coordinate_ref.slot) {
                    .position, .holomorphic => pair.holomorphic_derivatives,
                    .antiholomorphic => pair.antiholomorphic_derivatives,
                },
            };
        }

        fn label(self: WickPair, label_ref: wick.LabelRef) ?kernel.Call.LabelValue {
            const op = self.sideOp(label_ref.side);
            const index: usize = @as(usize, @intCast(op.labels)) + label_ref.slot;
            if (index >= self.labels.values.len) return null;
            return self.labels.values[index];
        }

        fn configValue(self: WickPair, config_ref: ConfigRef) ?ConfigValue {
            for (self.config.config_entries) |entry| {
                if (entry.id == config_ref) return entry.value;
            }
            return null;
        }
    };

    /// WickResidualRef points to one surviving original input occurrence.
    const WickResidualRef = struct {
        input_index: usize,
        operator: kernel.Call.LocalOp,
    };

    /// ResolvedCoordinateRef is one concrete coordinate variable with its derivative count.
    const ResolvedCoordinateRef = struct {
        variable: coefficient.Variable,
        derivatives: u8,
    };

    /// ResolvedCoordinateDifference is a concrete coordinate difference read by a Wick factor.
    const ResolvedCoordinateDifference = struct {
        left: ResolvedCoordinateRef,
        right: ResolvedCoordinateRef,
    };

    /// ResolvedDerivativeAction records the derivative counts requested by one coordinate factor.
    const ResolvedDerivativeAction = struct {
        left: ?u8 = null,
        right: ?u8 = null,
    };

    /// ResolvedTensorRef is tensor data resolved either from an operator label or config entry.
    const ResolvedTensorRef = union(enum) {
        label: kernel.Call.LabelValue,
        config: ConfigValue,
    };

    /// ResolvedScalarFactor is a scalar factor with all label references plugged in.
    const ResolvedScalarFactor = union(enum) {
        value: RuleScalar,
        label_bilinear_phase: struct { left: kernel.Call.LabelValue, right: kernel.Call.LabelValue, form: []const u8 },
        cocycle: struct { table: []const u8, left: kernel.Call.LabelValue, right: kernel.Call.LabelValue },
        spin_structure: []const u8,
    };

    /// ResolvedTensorFactor is a tensor multiplier with concrete labels and config values.
    const ResolvedTensorFactor = union(enum) {
        none,
        metric: struct { left: kernel.Call.LabelValue, right: kernel.Call.LabelValue },
        momentum_index: struct { momentum: kernel.Call.LabelValue, index: kernel.Call.LabelValue },
        momentum_pair: struct { left: kernel.Call.LabelValue, right: kernel.Call.LabelValue },
        projector_metric: struct { projector: ResolvedTensorRef, left: kernel.Call.LabelValue, right: kernel.Call.LabelValue },
        projector_momentum_index: struct { projector: ResolvedTensorRef, momentum: kernel.Call.LabelValue, index: kernel.Call.LabelValue },
        projector_momentum_pair: struct { projector: ResolvedTensorRef, left: kernel.Call.LabelValue, right: kernel.Call.LabelValue },
    };

    /// ResolvedActionFactor is a Wick action with concrete profile, index, and projector data.
    const ResolvedActionFactor = union(enum) {
        profile_derivative: struct { profile: kernel.Call.LabelValue, index: kernel.Call.LabelValue },
        projected_profile_derivative: struct { projector: ResolvedTensorRef, profile: kernel.Call.LabelValue, index: kernel.Call.LabelValue },
    };

    /// ResolvedCoordinateFactor is a coordinate kernel with concrete coordinates and derivative data.
    const ResolvedCoordinateFactor = union(enum) {
        difference_power: struct { coordinate: ResolvedCoordinateDifference, exponent: i16, derivatives: ResolvedDerivativeAction },
        logarithm: struct { coordinate: ResolvedCoordinateDifference, derivatives: ResolvedDerivativeAction },
        green_kernel: struct { name: []const u8, coordinate: ResolvedCoordinateDifference, derivatives: ResolvedDerivativeAction },
        green_exponential: ResolvedCoordinateDifference,
    };

    /// ResolvedTerm is one Wick term whose factors can be resolved without allocation.
    const ResolvedTerm = struct {
        pair: WickPair,
        source: *const wick.Term,

        fn scalarCount(self: ResolvedTerm) usize {
            return self.source.scalars.len;
        }

        fn coordinateCount(self: ResolvedTerm) usize {
            return self.source.coordinates.len;
        }

        fn tensorCount(self: ResolvedTerm) usize {
            return self.source.tensors.len;
        }

        fn actionCount(self: ResolvedTerm) usize {
            return self.source.actions.len;
        }

        fn residualCount(self: ResolvedTerm) usize {
            return self.source.residuals.len;
        }

        fn scalar(self: ResolvedTerm, index: usize) ?ResolvedScalarFactor {
            if (index >= self.source.scalars.len) return null;
            return resolveScalarFactor(self.pair, self.source.scalars[index]);
        }

        fn coordinate(self: ResolvedTerm, index: usize) ?ResolvedCoordinateFactor {
            if (index >= self.source.coordinates.len) return null;
            return resolveCoordinateFactor(self.pair, self.source.coordinates[index]);
        }

        fn tensor(self: ResolvedTerm, index: usize) ?ResolvedTensorFactor {
            if (index >= self.source.tensors.len) return null;
            return resolveTensorFactor(self.pair, self.source.tensors[index]);
        }

        fn action(self: ResolvedTerm, index: usize) ?ResolvedActionFactor {
            if (index >= self.source.actions.len) return null;
            return resolveActionFactor(self.pair, self.source.actions[index]);
        }

        fn residual(self: ResolvedTerm, index: usize) ?wick.Side {
            if (index >= self.source.residuals.len) return null;
            return self.source.residuals[index];
        }
    };

    /// ResolvedWickPair gives allocation-free access to concrete Wick terms for one pair.
    const ResolvedWickPair = struct {
        pair: WickPair,

        fn termCount(self: ResolvedWickPair) usize {
            return self.pair.rule.expr.terms.len;
        }

        fn term(self: ResolvedWickPair, index: usize) ?ResolvedTerm {
            if (index >= self.pair.rule.expr.terms.len) return null;
            return .{ .pair = self.pair, .source = &self.pair.rule.expr.terms[index] };
        }
    };

    /// PrimitiveWickTerm is one complete primitive Wick contribution without later simplification.
    const PrimitiveWickTerm = struct {
        resolved: ResolvedTerm,

        fn scalarCount(self: PrimitiveWickTerm) usize {
            return self.resolved.scalarCount();
        }

        fn coordinateCount(self: PrimitiveWickTerm) usize {
            return self.resolved.coordinateCount();
        }

        fn tensorCount(self: PrimitiveWickTerm) usize {
            return self.resolved.tensorCount();
        }

        fn actionCount(self: PrimitiveWickTerm) usize {
            return self.resolved.actionCount();
        }

        fn residualCount(self: PrimitiveWickTerm) usize {
            return self.resolved.residualCount();
        }

        fn scalar(self: PrimitiveWickTerm, index: usize) ?ResolvedScalarFactor {
            return self.resolved.scalar(index);
        }

        fn coordinate(self: PrimitiveWickTerm, index: usize) ?coefficient.CoordinateFactor {
            const factor = self.resolved.coordinate(index) orelse return null;
            return evaluateCoordinateFactor(factor);
        }

        fn tensor(self: PrimitiveWickTerm, index: usize) ?ResolvedTensorFactor {
            return self.resolved.tensor(index);
        }

        fn action(self: PrimitiveWickTerm, index: usize) ?ResolvedActionFactor {
            return self.resolved.action(index);
        }

        fn residual(self: PrimitiveWickTerm, index: usize) ?wick.Side {
            return self.resolved.residual(index);
        }
    };

    /// PrimitiveWickPair gives allocation-free complete terms for one primitive Wick pair.
    const PrimitiveWickPair = struct {
        pair: WickPair,

        fn termCount(self: PrimitiveWickPair) usize {
            return self.pair.rule.expr.terms.len;
        }

        fn term(self: PrimitiveWickPair, index: usize) ?PrimitiveWickTerm {
            const resolved = (ResolvedWickPair{ .pair = self.pair }).term(index) orelse return null;
            return .{ .resolved = resolved };
        }
    };

    fn resolveCoordinateRef(pair: WickPair, coordinate_ref: wick.CoordinateRef) ?ResolvedCoordinateRef {
        return .{
            .variable = pair.coordinate(coordinate_ref) orelse return null,
            .derivatives = pair.derivativeCount(coordinate_ref) orelse return null,
        };
    }

    fn resolveCoordinateDifference(pair: WickPair, difference: wick.CoordinateDifference) ?ResolvedCoordinateDifference {
        return .{
            .left = resolveCoordinateRef(pair, difference.left) orelse return null,
            .right = resolveCoordinateRef(pair, difference.right) orelse return null,
        };
    }

    fn resolveDerivativeAction(pair: WickPair, coordinate: wick.CoordinateDifference, action: wick.DerivativeAction) ?ResolvedDerivativeAction {
        return .{
            .left = if (action.include_left) pair.derivativeCount(coordinate.left) orelse return null else null,
            .right = if (action.include_right) pair.derivativeCount(coordinate.right) orelse return null else null,
        };
    }

    fn resolveTensorRef(pair: WickPair, tensor_ref: wick.TensorRef) ?ResolvedTensorRef {
        return switch (tensor_ref) {
            .label => |label_ref| .{ .label = pair.label(label_ref) orelse return null },
            .config => |config_ref| .{ .config = pair.configValue(config_ref) orelse return null },
        };
    }

    fn resolveScalarFactor(pair: WickPair, factor: wick.ScalarFactor) ?ResolvedScalarFactor {
        return switch (factor) {
            .value => |value| .{ .value = value },
            .label_bilinear_phase => |phase| .{ .label_bilinear_phase = .{
                .left = pair.label(phase.left) orelse return null,
                .right = pair.label(phase.right) orelse return null,
                .form = phase.form,
            } },
            .cocycle => |cocycle| .{ .cocycle = .{
                .table = cocycle.table,
                .left = pair.label(cocycle.left) orelse return null,
                .right = pair.label(cocycle.right) orelse return null,
            } },
            .spin_structure => |spin_structure| .{ .spin_structure = spin_structure },
        };
    }

    fn resolveTensorFactor(pair: WickPair, factor: wick.TensorFactor) ?ResolvedTensorFactor {
        return switch (factor) {
            .none => .none,
            .metric => |metric| .{ .metric = .{
                .left = pair.label(metric.left) orelse return null,
                .right = pair.label(metric.right) orelse return null,
            } },
            .momentum_index => |item| .{ .momentum_index = .{
                .momentum = pair.label(item.momentum) orelse return null,
                .index = pair.label(item.index) orelse return null,
            } },
            .momentum_pair => |item| .{ .momentum_pair = .{
                .left = pair.label(item.left) orelse return null,
                .right = pair.label(item.right) orelse return null,
            } },
            .projector_metric => |item| .{ .projector_metric = .{
                .projector = resolveTensorRef(pair, item.projector) orelse return null,
                .left = pair.label(item.left) orelse return null,
                .right = pair.label(item.right) orelse return null,
            } },
            .projector_momentum_index => |item| .{ .projector_momentum_index = .{
                .projector = resolveTensorRef(pair, item.projector) orelse return null,
                .momentum = pair.label(item.momentum) orelse return null,
                .index = pair.label(item.index) orelse return null,
            } },
            .projector_momentum_pair => |item| .{ .projector_momentum_pair = .{
                .projector = resolveTensorRef(pair, item.projector) orelse return null,
                .left = pair.label(item.left) orelse return null,
                .right = pair.label(item.right) orelse return null,
            } },
        };
    }

    fn resolveActionFactor(pair: WickPair, factor: wick.ActionFactor) ?ResolvedActionFactor {
        return switch (factor) {
            .profile_derivative => |item| .{ .profile_derivative = .{
                .profile = pair.label(item.profile) orelse return null,
                .index = pair.label(item.index) orelse return null,
            } },
            .projected_profile_derivative => |item| .{ .projected_profile_derivative = .{
                .projector = resolveTensorRef(pair, item.projector) orelse return null,
                .profile = pair.label(item.profile) orelse return null,
                .index = pair.label(item.index) orelse return null,
            } },
        };
    }

    fn resolveCoordinateFactor(pair: WickPair, factor: wick.CoordinateFactor) ?ResolvedCoordinateFactor {
        return switch (factor) {
            .difference_power => |item| .{ .difference_power = .{
                .coordinate = resolveCoordinateDifference(pair, item.coordinate) orelse return null,
                .exponent = item.exponent,
                .derivatives = resolveDerivativeAction(pair, item.coordinate, item.derivatives) orelse return null,
            } },
            .logarithm => |item| .{ .logarithm = .{
                .coordinate = resolveCoordinateDifference(pair, item.coordinate) orelse return null,
                .derivatives = resolveDerivativeAction(pair, item.coordinate, item.derivatives) orelse return null,
            } },
            .green_kernel => |item| .{ .green_kernel = .{
                .name = item.name,
                .coordinate = resolveCoordinateDifference(pair, item.coordinate) orelse return null,
                .derivatives = resolveDerivativeAction(pair, item.coordinate, item.derivatives) orelse return null,
            } },
            .green_exponential => |coordinate| .{ .green_exponential = resolveCoordinateDifference(pair, coordinate) orelse return null },
        };
    }

    fn coordinateDifference(coordinate: ResolvedCoordinateDifference) coefficient.CoordinateDifference {
        return .{
            .left = coordinate.left.variable,
            .right = coordinate.right.variable,
        };
    }

    fn selectedDerivativeCount(action: ResolvedDerivativeAction) u16 {
        const left: u16 = if (action.left) |count| count else 0;
        const right: u16 = if (action.right) |count| count else 0;
        return left + right;
    }

    fn selectedRightDerivativeCount(action: ResolvedDerivativeAction) u16 {
        return if (action.right) |count| count else 0;
    }

    fn checkedMulInt(left: i64, right: i64) ?i64 {
        const result = @mulWithOverflow(left, right);
        if (result[1] != 0) return null;
        return result[0];
    }

    fn checkedAddExponent(exponent: i16, derivative_count: u16) ?i16 {
        const next = @as(i32, exponent) - @as(i32, derivative_count);
        if (next < std.math.minInt(i16) or next > std.math.maxInt(i16)) return null;
        return @intCast(next);
    }

    fn fallingPower(exponent: i16, derivative_count: u16) ?i64 {
        var value: i64 = 1;
        var current: i64 = exponent;
        var index: u16 = 0;
        while (index < derivative_count) : (index += 1) {
            value = checkedMulInt(value, current) orelse return null;
            current -= 1;
        }
        return value;
    }

    fn factorial(value: u16) ?i64 {
        var result: i64 = 1;
        var current: u16 = 2;
        while (current <= value) : (current += 1) {
            result = checkedMulInt(result, current) orelse return null;
        }
        return result;
    }

    fn signFromParity(power: u16) i64 {
        return if ((power & 1) == 0) 1 else -1;
    }

    fn evaluateDifferencePower(item: anytype) ?coefficient.CoordinateFactor {
        const derivative_count = selectedDerivativeCount(item.derivatives);
        const right_count = selectedRightDerivativeCount(item.derivatives);
        const falling = fallingPower(item.exponent, derivative_count) orelse return null;
        const signed = checkedMulInt(signFromParity(right_count), falling) orelse return null;
        return .{
            .scalar = coefficient.rational(signed, 1) orelse return null,
            .kernel = .{ .difference_power = .{
                .coordinate = coordinateDifference(item.coordinate),
                .exponent = checkedAddExponent(item.exponent, derivative_count) orelse return null,
            } },
        };
    }

    fn evaluateLogarithm(item: anytype) ?coefficient.CoordinateFactor {
        const derivative_count = selectedDerivativeCount(item.derivatives);
        if (derivative_count == 0) {
            return .{
                .scalar = coefficient.integer(1),
                .kernel = .{ .logarithm = coordinateDifference(item.coordinate) },
            };
        }

        const right_count = selectedRightDerivativeCount(item.derivatives);
        const base = factorial(derivative_count - 1) orelse return null;
        const signed = checkedMulInt(signFromParity(right_count + derivative_count - 1), base) orelse return null;
        return .{
            .scalar = coefficient.rational(signed, 1) orelse return null,
            .kernel = .{ .difference_power = .{
                .coordinate = coordinateDifference(item.coordinate),
                .exponent = -@as(i16, @intCast(derivative_count)),
            } },
        };
    }

    fn evaluateGreenKernel(item: anytype) coefficient.CoordinateFactor {
        return .{
            .scalar = coefficient.integer(1),
            .kernel = .{ .green_kernel = .{
                .name = item.name,
                .coordinate = coordinateDifference(item.coordinate),
                .left_derivatives = if (item.derivatives.left) |count| count else 0,
                .right_derivatives = if (item.derivatives.right) |count| count else 0,
            } },
        };
    }

    fn evaluateCoordinateFactor(factor: ResolvedCoordinateFactor) ?coefficient.CoordinateFactor {
        return switch (factor) {
            .difference_power => |item| evaluateDifferencePower(item),
            .logarithm => |item| evaluateLogarithm(item),
            .green_kernel => |item| evaluateGreenKernel(item),
            .green_exponential => |coordinate| .{
                .scalar = coefficient.integer(1),
                .kernel = .{ .green_exponential = coordinateDifference(coordinate) },
            },
        };
    }

    const WickTermEvent = struct {
        left_index: usize,
        right_index: usize,
        term_index: usize,
    };

    const MatchedWickTerm = struct {
        pair: WickPair,
        rule_index: usize,
        term_index: usize,
    };
};

const ZeroModeRuntime = struct {
    const ResidualCursor = struct {
        ops: kernel.Call.MultiOp,
        indices: ?[]const usize,

        fn len(self: ResidualCursor) usize {
            return if (self.indices) |indices| indices.len else self.ops.operators.len;
        }

        fn opIndex(self: ResidualCursor, residual_index: usize) usize {
            return if (self.indices) |indices| indices[residual_index] else residual_index;
        }

        fn op(self: ResidualCursor, residual_index: usize) kernel.Call.LocalOp {
            return self.ops.operators[self.opIndex(residual_index)];
        }
    };

    const CJet = struct {
        coordinate: coefficient.Variable,
        derivative_order: u8,
    };

    const MomentumDelta = struct {
        projector: ?ConfigValue,
        momenta: []const kernel.Call.LabelValue,
        two_pi_power: u16,
        scalar: RuleScalar,
    };

    const DirichletPhase = struct {
        projector: ConfigValue,
        position: ConfigValue,
        momenta: []const kernel.Call.LabelValue,
    };

    const ProfileFactor = struct {
        profile: kernel.Call.LabelValue,
        coordinate: coefficient.Variable,
    };

    const ZeroModeFactor = union(enum) {
        bc_top_form: struct {
            support: zero_mode.BcSupport,
            normalization: RuleScalar,
            jets: [3]CJet,
        },
        eta_xi_zero_mode: struct {
            support: zero_mode.EtaXiSupport,
            normalization: RuleScalar,
            xi: CJet,
        },
        momentum_delta: MomentumDelta,
        dirichlet_phase: DirichletPhase,
        profile_fourier_integral: ProfileFactor,
        profile_polynomial_integral: ProfileFactor,
        profile_gaussian_differential: ProfileFactor,
    };
};

const TextBudget = enum {
    small,
    medium,
};

/// text exposes bounded result-inspection sinks.
pub const text = struct {
    /// compact returns a writer-backed sink for small symbolic correlators.
    pub fn compact(writer: anytype, comptime budget: TextBudget) CompactTextSink(@TypeOf(writer), budget) {
        return .{ .writer = writer };
    }
};

fn textByteLimit(comptime budget: TextBudget) usize {
    return switch (budget) {
        .small => 4096,
        .medium => 65536,
    };
}

fn textBranchLimit(comptime budget: TextBudget) usize {
    return switch (budget) {
        .small => 32,
        .medium => 1024,
    };
}

fn CompactTextSink(comptime Writer: type, comptime budget: TextBudget) type {
    return struct {
        const Self = @This();

        writer: Writer,
        bytes_written: usize = 0,
        branch_count: usize = 0,
        branch_open: bool = false,
        branch_has_factor: bool = false,
        term_open: bool = false,
        term_has_factor: bool = false,
        pending_sign: i8 = 1,

        fn writeAll(self: *Self, bytes: []const u8) !void {
            if (self.bytes_written + bytes.len > textByteLimit(budget)) return error.RenderLimitExceeded;
            try self.writer.writeAll(bytes);
            self.bytes_written += bytes.len;
        }

        fn writeFmt(self: *Self, comptime fmt: []const u8, args: anytype) !void {
            var buffer: [256]u8 = undefined;
            const rendered = std.fmt.bufPrint(&buffer, fmt, args) catch return error.RenderLimitExceeded;
            try self.writeAll(rendered);
        }

        fn beginBranch(self: *Self) !void {
            if (self.branch_open) return;
            if (self.branch_count == textBranchLimit(budget)) return error.RenderLimitExceeded;
            if (self.branch_count != 0) {
                try self.writeAll(if (self.pending_sign < 0) " - " else " + ");
            } else if (self.pending_sign < 0) {
                try self.writeAll("-");
            }
            self.branch_open = true;
            self.branch_has_factor = false;
            self.pending_sign = 1;
        }

        fn factorSeparator(self: *Self) !void {
            try self.beginBranch();
            if (self.term_open) {
                if (self.term_has_factor) try self.writeAll("*");
                self.term_has_factor = true;
                return;
            }
            if (self.branch_has_factor) try self.writeAll("*");
            self.branch_has_factor = true;
        }

        fn writeRational(self: *Self, value: RationalScalar) !void {
            if (value.denominator == 1) return self.writeFmt("{}", .{value.numerator});
            return self.writeFmt("{}/{}", .{ value.numerator, value.denominator });
        }

        fn writeRuleScalar(self: *Self, value: RuleScalar) !void {
            switch (value) {
                .one => try self.writeAll("1"),
                .rational => |rational| try self.writeRational(rational),
                .monomial => |monomial| {
                    try self.writeRational(monomial.rational);
                    if (monomial.imaginary_power != 0) try self.writeFmt("*i^{}", .{monomial.imaginary_power});
                    if (monomial.atom) |atom| try self.writeFmt("*s{}^{}", .{ atom, monomial.atom_power });
                },
            }
        }

        fn writeLabel(self: *Self, value: kernel.Call.LabelValue) !void {
            switch (value) {
                .integer => |item| try self.writeFmt("{}", .{item}),
                .rational => |item| try self.writeFmt("{}/{}", .{ item.numerator, item.denominator }),
                .tensor => |item| try self.writeFmt("T{}", .{item}),
                .symbol => |item| try self.writeFmt("q{}", .{item}),
            }
        }

        fn writeConfig(self: *Self, value: ConfigValue) !void {
            switch (value) {
                .tensor_projector => |item| try self.writeFmt("P{}", .{@intFromEnum(item)}),
                .target_point => |item| try self.writeFmt("x{}", .{@intFromEnum(item)}),
                .target_dimension => |item| try self.writeFmt("D{}", .{item}),
                .boundary_stack => |item| try self.writeFmt("CP{}", .{@intFromEnum(item)}),
            }
        }

        fn writeTensorRef(self: *Self, value: Correlator.ResolvedTensorRef) !void {
            switch (value) {
                .label => |item| try self.writeLabel(item),
                .config => |item| try self.writeConfig(item),
            }
        }

        fn writeCoordinateDifference(self: *Self, value: coefficient.CoordinateDifference) !void {
            try self.writeFmt("(z{}-z{})", .{ value.left, value.right });
        }

        pub fn emitWickBranchSign(self: *Self, sign: i8) !void {
            if (sign < 0) self.pending_sign = -1;
        }

        pub fn emitWickBranchTerm(self: *Self, branch: anytype) !void {
            const Proxy = struct {
                renderer: *Self,

                pub fn emitWickTermStart(proxy: *@This(), event: Correlator.WickTermEvent) !void {
                    try proxy.renderer.emitWickTermStart(event);
                }

                pub fn emitWickScalar(proxy: *@This(), factor: Correlator.ResolvedScalarFactor) !void {
                    try proxy.renderer.emitWickScalar(factor);
                }

                pub fn emitWickCoordinate(proxy: *@This(), factor: coefficient.CoordinateFactor) !void {
                    try proxy.renderer.emitWickCoordinate(factor);
                }

                pub fn emitWickTensor(proxy: *@This(), factor: Correlator.ResolvedTensorFactor) !void {
                    try proxy.renderer.emitWickTensor(factor);
                }

                pub fn emitWickAction(proxy: *@This(), factor: Correlator.ResolvedActionFactor) !void {
                    try proxy.renderer.emitWickAction(factor);
                }

                pub fn emitWickResidualOperator(proxy: *@This(), residual: Correlator.WickResidualRef) !void {
                    try proxy.renderer.emitWickResidualOperator(residual);
                }

                pub fn emitWickTermEnd(proxy: *@This()) !void {
                    try proxy.renderer.emitWickTermEnd();
                }
            };

            var proxy = Proxy{ .renderer = self };
            try branch.emit(&proxy);
        }

        pub fn emitWickTermStart(self: *Self, _: Correlator.WickTermEvent) !void {
            try self.factorSeparator();
            try self.writeAll("(");
            self.term_open = true;
            self.term_has_factor = false;
        }

        pub fn emitWickScalar(self: *Self, factor: Correlator.ResolvedScalarFactor) !void {
            try self.factorSeparator();
            switch (factor) {
                .value => |value| try self.writeRuleScalar(value),
                .label_bilinear_phase => |item| {
                    try self.writeFmt("phase[{s}](", .{item.form});
                    try self.writeLabel(item.left);
                    try self.writeAll(",");
                    try self.writeLabel(item.right);
                    try self.writeAll(")");
                },
                .cocycle => |item| {
                    try self.writeFmt("cocycle[{s}](", .{item.table});
                    try self.writeLabel(item.left);
                    try self.writeAll(",");
                    try self.writeLabel(item.right);
                    try self.writeAll(")");
                },
                .spin_structure => |name| try self.writeFmt("spin[{s}]", .{name}),
            }
        }

        pub fn emitWickCoordinate(self: *Self, factor: coefficient.CoordinateFactor) !void {
            try self.factorSeparator();
            if (factor.scalar.numerator != 1 or factor.scalar.denominator != 1) {
                try self.writeFmt("{}/{}*", .{ factor.scalar.numerator, factor.scalar.denominator });
            }
            switch (factor.kernel) {
                .difference_power => |item| {
                    try self.writeCoordinateDifference(item.coordinate);
                    try self.writeFmt("^{}", .{item.exponent});
                },
                .logarithm => |coordinate| {
                    try self.writeAll("log");
                    try self.writeCoordinateDifference(coordinate);
                },
                .green_kernel => |item| {
                    try self.writeFmt("G[{s};{},{}]", .{ item.name, item.left_derivatives, item.right_derivatives });
                    try self.writeCoordinateDifference(item.coordinate);
                },
                .green_exponential => |coordinate| {
                    try self.writeAll("expG");
                    try self.writeCoordinateDifference(coordinate);
                },
            }
        }

        pub fn emitWickTensor(self: *Self, factor: Correlator.ResolvedTensorFactor) !void {
            try self.factorSeparator();
            switch (factor) {
                .none => try self.writeAll("1"),
                .metric => |item| {
                    try self.writeAll("eta(");
                    try self.writeLabel(item.left);
                    try self.writeAll(",");
                    try self.writeLabel(item.right);
                    try self.writeAll(")");
                },
                .momentum_index => |item| {
                    try self.writeAll("p(");
                    try self.writeLabel(item.momentum);
                    try self.writeAll("; ");
                    try self.writeLabel(item.index);
                    try self.writeAll(")");
                },
                .momentum_pair => |item| {
                    try self.writeAll("p(");
                    try self.writeLabel(item.left);
                    try self.writeAll(").p(");
                    try self.writeLabel(item.right);
                    try self.writeAll(")");
                },
                .projector_metric => |item| {
                    try self.writeAll("eta[");
                    try self.writeTensorRef(item.projector);
                    try self.writeAll("](");
                    try self.writeLabel(item.left);
                    try self.writeAll(",");
                    try self.writeLabel(item.right);
                    try self.writeAll(")");
                },
                .projector_momentum_index => |item| {
                    try self.writeAll("p[");
                    try self.writeTensorRef(item.projector);
                    try self.writeAll("](");
                    try self.writeLabel(item.momentum);
                    try self.writeAll("; ");
                    try self.writeLabel(item.index);
                    try self.writeAll(")");
                },
                .projector_momentum_pair => |item| {
                    try self.writeAll("p[");
                    try self.writeTensorRef(item.projector);
                    try self.writeAll("](");
                    try self.writeLabel(item.left);
                    try self.writeAll(",");
                    try self.writeLabel(item.right);
                    try self.writeAll(")");
                },
            }
        }

        pub fn emitWickAction(self: *Self, factor: Correlator.ResolvedActionFactor) !void {
            try self.factorSeparator();
            switch (factor) {
                .profile_derivative => |item| {
                    try self.writeAll("dProfile(");
                    try self.writeLabel(item.profile);
                    try self.writeAll(",");
                    try self.writeLabel(item.index);
                    try self.writeAll(")");
                },
                .projected_profile_derivative => |item| {
                    try self.writeAll("dProfile[");
                    try self.writeTensorRef(item.projector);
                    try self.writeAll("](");
                    try self.writeLabel(item.profile);
                    try self.writeAll(",");
                    try self.writeLabel(item.index);
                    try self.writeAll(")");
                },
            }
        }

        pub fn emitWickResidualOperator(self: *Self, residual: Correlator.WickResidualRef) !void {
            try self.factorSeparator();
            try self.writeFmt("op{}", .{residual.input_index});
        }

        pub fn emitWickTermEnd(self: *Self) !void {
            if (!self.term_has_factor) try self.writeAll("1");
            try self.writeAll(")");
            self.term_open = false;
            self.branch_has_factor = true;
        }

        pub fn emitZeroModeFactor(self: *Self, factor: ZeroModeRuntime.ZeroModeFactor) !void {
            try self.factorSeparator();
            switch (factor) {
                .bc_top_form => |item| try self.writeFmt("bcTop[{s}]", .{@tagName(item.support)}),
                .eta_xi_zero_mode => |item| try self.writeFmt("etaXiZero[{s};z{}]", .{ @tagName(item.support), item.xi.coordinate }),
                .momentum_delta => |item| try self.writeFmt("deltaP[{}]", .{item.momenta.len}),
                .dirichlet_phase => |item| {
                    try self.writeAll("dirichletPhase[");
                    try self.writeConfig(item.projector);
                    try self.writeAll(",");
                    try self.writeConfig(item.position);
                    try self.writeAll("]");
                },
                .profile_fourier_integral => |item| {
                    try self.writeAll("profileFourier(");
                    try self.writeLabel(item.profile);
                    try self.writeFmt(";z{})", .{item.coordinate});
                },
                .profile_polynomial_integral => |item| {
                    try self.writeAll("profilePolynomial(");
                    try self.writeLabel(item.profile);
                    try self.writeFmt(";z{})", .{item.coordinate});
                },
                .profile_gaussian_differential => |item| {
                    try self.writeAll("profileGaussian(");
                    try self.writeLabel(item.profile);
                    try self.writeFmt(";z{})", .{item.coordinate});
                },
            }
        }

        pub fn emitZeroModeBaseEnd(self: *Self) !void {
            try self.beginBranch();
            if (!self.branch_has_factor) try self.writeAll("1");
            self.branch_open = false;
            self.branch_has_factor = false;
            self.branch_count += 1;
        }
    };
}

fn residualConsumed(mask: u128, index: usize) bool {
    return (mask & (@as(u128, 1) << @intCast(index))) != 0;
}

fn markResidualConsumed(mask: *u128, index: usize) void {
    mask.* |= @as(u128, 1) << @intCast(index);
}

fn kindIn(kind: operators.OperatorKindId, candidates: []const operators.OperatorKindId) bool {
    for (candidates) |candidate| {
        if (candidate == kind) return true;
    }
    return false;
}

fn localPosition(op: kernel.Call.LocalOp) ?coefficient.Variable {
    return switch (op.insertion) {
        .single => |single| single.position,
        .pair => |pair| pair.holomorphic_position,
    };
}

fn localDerivativeOrder(op: kernel.Call.LocalOp) u8 {
    return switch (op.insertion) {
        .single => |single| single.derivatives,
        .pair => |pair| pair.holomorphic_derivatives,
    };
}

fn firstLabel(ops: kernel.Call.MultiOp, op: kernel.Call.LocalOp) ?kernel.Call.LabelValue {
    const index: usize = @intCast(op.labels);
    if (index >= ops.labels.values.len) return null;
    return ops.labels.values[index];
}

fn configValue(config_ptr: *const CorrelatorConfigData, config_ref: ConfigRef) ?ConfigValue {
    for (config_ptr.config_entries) |entry| {
        if (entry.id == config_ref) return entry.value;
    }
    return null;
}

fn projectorRank(value: ConfigValue) ?u16 {
    return switch (value) {
        .tensor_projector => |projector| @intCast(@intFromEnum(projector) >> 24),
        else => null,
    };
}

fn rankValue(config_ptr: *const CorrelatorConfigData, source: zero_mode.RankSource) ?u16 {
    return switch (source) {
        .none => 0,
        .literal => |value| value,
        .target_dimension => |config_ref| switch (configValue(config_ptr, config_ref) orelse return null) {
            .target_dimension => |dimension| dimension,
            else => null,
        },
        .projector_rank => |config_ref| projectorRank(configValue(config_ptr, config_ref) orelse return null),
    };
}

fn hasRankSource(source: zero_mode.RankSource) bool {
    return switch (source) {
        .none => false,
        else => true,
    };
}

fn emitBcTopForm(rule: zero_mode.BcTopForm, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128, sink: anytype) !void {
    var jets: [3]ZeroModeRuntime.CJet = undefined;
    var residual_ids: [3]usize = undefined;
    var jet_count: usize = 0;
    var overflow = false;

    var residual_index: usize = 0;
    while (residual_index < residual.len()) : (residual_index += 1) {
        if (residualConsumed(consumed.*, residual_index)) continue;
        const op = residual.op(residual_index);
        if (!kindIn(op.kind, rule.c_kind_ids)) continue;
        if (jet_count >= jets.len) {
            overflow = true;
            continue;
        }
        jets[jet_count] = .{
            .coordinate = localPosition(op) orelse return error.InvalidZeroModeOperator,
            .derivative_order = localDerivativeOrder(op),
        };
        residual_ids[jet_count] = residual_index;
        jet_count += 1;
    }

    if (overflow or jet_count != 3) return;
    for (residual_ids) |residual_id| {
        markResidualConsumed(consumed, residual_id);
    }
    try sink.emitZeroModeFactor(ZeroModeRuntime.ZeroModeFactor{ .bc_top_form = .{
        .support = rule.support,
        .normalization = rule.normalization,
        .jets = jets,
    } });
}

fn acceptBcTopForm(rule: zero_mode.BcTopForm, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128) !void {
    var residual_ids: [3]usize = undefined;
    var jet_count: usize = 0;
    var overflow = false;

    var residual_index: usize = 0;
    while (residual_index < residual.len()) : (residual_index += 1) {
        if (residualConsumed(consumed.*, residual_index)) continue;
        const op = residual.op(residual_index);
        if (!kindIn(op.kind, rule.c_kind_ids)) continue;
        if (localPosition(op) == null) return error.InvalidZeroModeOperator;
        if (jet_count >= residual_ids.len) {
            overflow = true;
            continue;
        }
        residual_ids[jet_count] = residual_index;
        jet_count += 1;
    }

    if (overflow or jet_count != 3) return;
    for (residual_ids) |residual_id| {
        markResidualConsumed(consumed, residual_id);
    }
}

fn emitEtaXiZeroMode(rule: zero_mode.EtaXiZeroMode, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128, sink: anytype) !void {
    var xi: ZeroModeRuntime.CJet = undefined;
    var residual_id: usize = 0;
    var found = false;
    var overflow = false;

    var residual_index: usize = 0;
    while (residual_index < residual.len()) : (residual_index += 1) {
        if (residualConsumed(consumed.*, residual_index)) continue;
        const op = residual.op(residual_index);
        if (!kindIn(op.kind, rule.xi_kind_ids)) continue;
        if (localDerivativeOrder(op) != 0 or found) {
            overflow = true;
            continue;
        }
        xi = .{
            .coordinate = localPosition(op) orelse return error.InvalidZeroModeOperator,
            .derivative_order = 0,
        };
        residual_id = residual_index;
        found = true;
    }

    if (overflow or !found) return;
    markResidualConsumed(consumed, residual_id);
    try sink.emitZeroModeFactor(ZeroModeRuntime.ZeroModeFactor{ .eta_xi_zero_mode = .{
        .support = rule.support,
        .normalization = rule.normalization,
        .xi = xi,
    } });
}

fn acceptEtaXiZeroMode(rule: zero_mode.EtaXiZeroMode, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128) !void {
    var residual_id: usize = 0;
    var found = false;
    var overflow = false;

    var residual_index: usize = 0;
    while (residual_index < residual.len()) : (residual_index += 1) {
        if (residualConsumed(consumed.*, residual_index)) continue;
        const op = residual.op(residual_index);
        if (!kindIn(op.kind, rule.xi_kind_ids)) continue;
        if (localPosition(op) == null) return error.InvalidZeroModeOperator;
        if (localDerivativeOrder(op) != 0 or found) {
            overflow = true;
            continue;
        }
        residual_id = residual_index;
        found = true;
    }

    if (overflow or !found) return;
    markResidualConsumed(consumed, residual_id);
}

fn emitFreeBosonConstantMode(comptime limits: BranchLimits, config_ptr: *const CorrelatorConfigData, rule: zero_mode.FreeBosonConstantMode, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128, sink: anytype) !void {
    var momenta: [limits.max_zero_mode_items]kernel.Call.LabelValue = undefined;
    var momentum_count: usize = 0;

    var residual_index: usize = 0;
    while (residual_index < residual.len()) : (residual_index += 1) {
        if (residualConsumed(consumed.*, residual_index)) continue;
        const op = residual.op(residual_index);
        if (kindIn(op.kind, rule.exp_kind_ids)) {
            if (momentum_count >= momenta.len) return error.TooManyZeroModeItems;
            momenta[momentum_count] = firstLabel(residual.ops, op) orelse return error.InvalidZeroModeOperator;
            momentum_count += 1;
            markResidualConsumed(consumed, residual_index);
            continue;
        }

        if (kindIn(op.kind, rule.profile_kind_ids)) {
            const label = firstLabel(residual.ops, op) orelse return error.InvalidZeroModeOperator;
            const profile = switch (label) {
                .symbol => |value| @as(Handle.Profile, @enumFromInt(value)),
                else => return error.InvalidZeroModeOperator,
            };
            const factor = ZeroModeRuntime.ProfileFactor{
                .profile = label,
                .coordinate = localPosition(op) orelse return error.InvalidZeroModeOperator,
            };
            switch (profilePresentation(profile)) {
                .position_space => try sink.emitZeroModeFactor(ZeroModeRuntime.ZeroModeFactor{ .profile_gaussian_differential = factor }),
                .fourier => try sink.emitZeroModeFactor(ZeroModeRuntime.ZeroModeFactor{ .profile_fourier_integral = factor }),
                .polynomial_rnc => try sink.emitZeroModeFactor(ZeroModeRuntime.ZeroModeFactor{ .profile_polynomial_integral = factor }),
            }
            markResidualConsumed(consumed, residual_index);
        }
    }

    if (momentum_count != 0 or hasRankSource(rule.normalization.two_pi_power)) {
        const projector = if (rule.integration_projector) |config_ref| configValue(config_ptr, config_ref) orelse return error.InvalidZeroModeConfig else null;
        try sink.emitZeroModeFactor(ZeroModeRuntime.ZeroModeFactor{ .momentum_delta = .{
            .projector = projector,
            .momenta = momenta[0..momentum_count],
            .two_pi_power = rankValue(config_ptr, rule.normalization.two_pi_power) orelse return error.InvalidZeroModeConfig,
            .scalar = rule.normalization.scalar,
        } });
    }

    if (rule.fixed_projector) |projector_ref| {
        if (momentum_count == 0) return;
        const position_ref = rule.fixed_position orelse return error.InvalidZeroModeConfig;
        try sink.emitZeroModeFactor(ZeroModeRuntime.ZeroModeFactor{ .dirichlet_phase = .{
            .projector = configValue(config_ptr, projector_ref) orelse return error.InvalidZeroModeConfig,
            .position = configValue(config_ptr, position_ref) orelse return error.InvalidZeroModeConfig,
            .momenta = momenta[0..momentum_count],
        } });
    }
}

fn acceptFreeBosonConstantMode(comptime limits: BranchLimits, config_ptr: *const CorrelatorConfigData, rule: zero_mode.FreeBosonConstantMode, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128) !void {
    var momentum_count: usize = 0;

    var residual_index: usize = 0;
    while (residual_index < residual.len()) : (residual_index += 1) {
        if (residualConsumed(consumed.*, residual_index)) continue;
        const op = residual.op(residual_index);
        if (kindIn(op.kind, rule.exp_kind_ids)) {
            if (momentum_count >= limits.max_zero_mode_items) return error.TooManyZeroModeItems;
            _ = firstLabel(residual.ops, op) orelse return error.InvalidZeroModeOperator;
            momentum_count += 1;
            markResidualConsumed(consumed, residual_index);
            continue;
        }

        if (kindIn(op.kind, rule.profile_kind_ids)) {
            const label = firstLabel(residual.ops, op) orelse return error.InvalidZeroModeOperator;
            const profile = switch (label) {
                .symbol => |value| @as(Handle.Profile, @enumFromInt(value)),
                else => return error.InvalidZeroModeOperator,
            };
            _ = localPosition(op) orelse return error.InvalidZeroModeOperator;
            _ = profilePresentation(profile);
            markResidualConsumed(consumed, residual_index);
        }
    }

    if (momentum_count != 0 or hasRankSource(rule.normalization.two_pi_power)) {
        if (rule.integration_projector) |config_ref| _ = configValue(config_ptr, config_ref) orelse return error.InvalidZeroModeConfig;
        _ = rankValue(config_ptr, rule.normalization.two_pi_power) orelse return error.InvalidZeroModeConfig;
    }

    if (rule.fixed_projector) |projector_ref| {
        if (momentum_count == 0) return;
        const position_ref = rule.fixed_position orelse return error.InvalidZeroModeConfig;
        _ = configValue(config_ptr, projector_ref) orelse return error.InvalidZeroModeConfig;
        _ = configValue(config_ptr, position_ref) orelse return error.InvalidZeroModeConfig;
    }
}

fn allResidualsConsumed(residual: ZeroModeRuntime.ResidualCursor, consumed: u128) bool {
    var residual_index: usize = 0;
    while (residual_index < residual.len()) : (residual_index += 1) {
        if (!residualConsumed(consumed, residual_index)) return false;
    }
    return true;
}

fn emitEmptyFreeBosonConstantMode(config_ptr: *const CorrelatorConfigData, rule: zero_mode.FreeBosonConstantMode, sink: anytype) !void {
    if (hasRankSource(rule.normalization.two_pi_power)) {
        const empty_momenta: [0]kernel.Call.LabelValue = .{};
        const projector = if (rule.integration_projector) |config_ref| configValue(config_ptr, config_ref) orelse return error.InvalidZeroModeConfig else null;
        try sink.emitZeroModeFactor(ZeroModeRuntime.ZeroModeFactor{ .momentum_delta = .{
            .projector = projector,
            .momenta = empty_momenta[0..],
            .two_pi_power = rankValue(config_ptr, rule.normalization.two_pi_power) orelse return error.InvalidZeroModeConfig,
            .scalar = rule.normalization.scalar,
        } });
    }
}

fn BcTopFormProcedure(comptime rule: zero_mode.BcTopForm) type {
    return struct {
        fn canConsumeKind(kind: operators.OperatorKindId) bool {
            return kindIn(kind, rule.c_kind_ids);
        }

        fn accept(comptime limits: BranchLimits, config_ptr: *const CorrelatorConfigData, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128) !void {
            _ = limits;
            _ = config_ptr;
            return acceptBcTopForm(rule, residual, consumed);
        }

        fn emit(comptime limits: BranchLimits, config_ptr: *const CorrelatorConfigData, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128, sink: anytype) !void {
            _ = limits;
            _ = config_ptr;
            return emitBcTopForm(rule, residual, consumed, sink);
        }

        fn emitEmpty(config_ptr: *const CorrelatorConfigData, sink: anytype) !void {
            _ = config_ptr;
            _ = sink;
        }
    };
}

fn EtaXiZeroModeProcedure(comptime rule: zero_mode.EtaXiZeroMode) type {
    return struct {
        fn canConsumeKind(kind: operators.OperatorKindId) bool {
            return kindIn(kind, rule.xi_kind_ids);
        }

        fn accept(comptime limits: BranchLimits, config_ptr: *const CorrelatorConfigData, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128) !void {
            _ = limits;
            _ = config_ptr;
            return acceptEtaXiZeroMode(rule, residual, consumed);
        }

        fn emit(comptime limits: BranchLimits, config_ptr: *const CorrelatorConfigData, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128, sink: anytype) !void {
            _ = limits;
            _ = config_ptr;
            return emitEtaXiZeroMode(rule, residual, consumed, sink);
        }

        fn emitEmpty(config_ptr: *const CorrelatorConfigData, sink: anytype) !void {
            _ = config_ptr;
            _ = sink;
        }
    };
}

fn ConstantFermionProcedure(comptime rule: zero_mode.ConstantFermion) type {
    const adapted = zero_mode.EtaXiZeroMode{
        .support = rule.support,
        .xi_kind_ids = rule.fermion_kind_ids,
        .normalization = rule.normalization,
    };
    return EtaXiZeroModeProcedure(adapted);
}

fn TopFormFermionProcedure(comptime rule: zero_mode.TopFormFermion) type {
    const adapted = zero_mode.BcTopForm{
        .support = rule.support,
        .c_kind_ids = rule.field_kind_ids,
        .normalization = rule.normalization,
    };
    return BcTopFormProcedure(adapted);
}

fn FreeBosonConstantModeProcedure(comptime rule: zero_mode.FreeBosonConstantMode) type {
    return struct {
        fn canConsumeKind(kind: operators.OperatorKindId) bool {
            return kindIn(kind, rule.exp_kind_ids) or kindIn(kind, rule.profile_kind_ids);
        }

        fn accept(comptime limits: BranchLimits, config_ptr: *const CorrelatorConfigData, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128) !void {
            return acceptFreeBosonConstantMode(limits, config_ptr, rule, residual, consumed);
        }

        fn emit(comptime limits: BranchLimits, config_ptr: *const CorrelatorConfigData, residual: ZeroModeRuntime.ResidualCursor, consumed: *u128, sink: anytype) !void {
            return emitFreeBosonConstantMode(limits, config_ptr, rule, residual, consumed, sink);
        }

        fn emitEmpty(config_ptr: *const CorrelatorConfigData, sink: anytype) !void {
            return emitEmptyFreeBosonConstantMode(config_ptr, rule, sink);
        }
    };
}

fn ZeroModeProcedure(comptime expr: zero_mode.Expr) type {
    return switch (expr) {
        .bc_top_form => |rule| BcTopFormProcedure(rule),
        .free_boson_constant_mode => |rule| FreeBosonConstantModeProcedure(rule),
        .eta_xi_zero_mode => |rule| EtaXiZeroModeProcedure(rule),
        .constant_fermion => |rule| ConstantFermionProcedure(rule),
        .top_form_fermion => |rule| TopFormFermionProcedure(rule),
        .boson_momentum_conservation => |rule| FreeBosonConstantModeProcedure(rule),
    };
}

fn generatedZeroModeCanConsumeKind(comptime ConfigHandle: type, kind: operators.OperatorKindId) bool {
    inline for (ConfigHandle.impl.zero_modes) |rule| {
        if (ZeroModeProcedure(rule.expr).canConsumeKind(kind)) return true;
    }
    return false;
}

fn generatedZeroModeCursorSucceeds(comptime ConfigHandle: type, config_ptr: *const CorrelatorConfigData, residual: ZeroModeRuntime.ResidualCursor) !bool {
    const limits = ConfigHandle.branch_limits;
    if (residual.len() > limits.max_zero_mode_residuals) return error.TooManyZeroModeResiduals;

    var consumed: u128 = 0;
    inline for (ConfigHandle.impl.zero_modes) |rule| {
        try ZeroModeProcedure(rule.expr).accept(limits, config_ptr, residual, &consumed);
    }

    return allResidualsConsumed(residual, consumed);
}

fn generatedZeroModeBaseCaseSucceeds(comptime ConfigHandle: type, config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, residual_indices: []const usize) !bool {
    if (residual_indices.len == 0) return true;
    const residual = ZeroModeRuntime.ResidualCursor{ .ops = ops, .indices = residual_indices };
    return generatedZeroModeCursorSucceeds(ConfigHandle, config_ptr, residual);
}

fn generatedEmptyZeroModeBaseCase(comptime ConfigHandle: type, config_ptr: *const CorrelatorConfigData, sink: anytype) !void {
    inline for (ConfigHandle.impl.zero_modes) |rule| {
        try ZeroModeProcedure(rule.expr).emitEmpty(config_ptr, sink);
    }
    try sink.emitZeroModeBaseEnd();
}

fn generatedTrustedZeroModeBaseCase(comptime ConfigHandle: type, config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, residual_indices: []const usize, sink: anytype) !void {
    const limits = ConfigHandle.branch_limits;
    if (residual_indices.len > limits.max_zero_mode_residuals) return error.TooManyZeroModeResiduals;
    if (residual_indices.len == 0) {
        try generatedEmptyZeroModeBaseCase(ConfigHandle, config_ptr, sink);
        return;
    }

    var consumed: u128 = 0;
    const residual = ZeroModeRuntime.ResidualCursor{ .ops = ops, .indices = residual_indices };
    // The branch walker has already dry-run validated these residuals.
    inline for (ConfigHandle.impl.zero_modes) |rule| {
        try ZeroModeProcedure(rule.expr).emit(limits, config_ptr, residual, &consumed, sink);
    }
    if (!allResidualsConsumed(residual, consumed)) return error.InvalidWickBranch;
    try sink.emitZeroModeBaseEnd();
}

/// generatedZeroModeBaseCase consumes residual operators with configured zero-mode procedures.
fn generatedZeroModeBaseCase(comptime ConfigHandle: type, config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, residual_indices: ?[]const usize, sink: anytype) !bool {
    const limits = ConfigHandle.branch_limits;
    const residual = ZeroModeRuntime.ResidualCursor{ .ops = ops, .indices = residual_indices };
    if (residual.len() > limits.max_zero_mode_residuals) return error.TooManyZeroModeResiduals;
    if (residual.len() == 0) {
        try generatedEmptyZeroModeBaseCase(ConfigHandle, config_ptr, sink);
        return true;
    }
    if (!try generatedZeroModeCursorSucceeds(ConfigHandle, config_ptr, residual)) return false;

    var consumed: u128 = 0;
    inline for (ConfigHandle.impl.zero_modes) |rule| {
        try ZeroModeProcedure(rule.expr).emit(limits, config_ptr, residual, &consumed, sink);
    }

    if (!allResidualsConsumed(residual, consumed)) return false;
    try sink.emitZeroModeBaseEnd();
    return true;
}

fn ruleMatches(rule: wick.Rule, left: kernel.Call.LocalOp, right: kernel.Call.LocalOp) ?bool {
    if (rule.left.kind == left.kind and rule.right.kind == right.kind) {
        return false;
    }
    if (rule.left.kind == right.kind and rule.right.kind == left.kind) {
        return true;
    }
    return null;
}

fn matchRule(config_ptr: *const CorrelatorConfigData, rule: *const wick.Rule, left: kernel.Call.LocalOp, right: kernel.Call.LocalOp, labels: *const kernel.Call.LabelStore) ?Correlator.WickPair {
    const reversed = ruleMatches(rule.*, left, right) orelse return null;
    return .{
        .rule = rule,
        .config = config_ptr,
        .left = left,
        .right = right,
        .labels = labels,
        .reversed = reversed,
    };
}

fn lowerBoundPairLookup(entries: []const PairLookupEntry, key: u64) usize {
    var lo: usize = 0;
    var hi: usize = entries.len;
    while (lo < hi) {
        const mid = lo + ((hi - lo) / 2);
        if (entries[mid].key < key) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    return lo;
}

fn emitPrimitiveWickTerm(pair: Correlator.WickPair, left_index: usize, right_index: usize, term_index: usize, sink: anytype) !void {
    const primitive = (Correlator.PrimitiveWickPair{ .pair = pair }).term(term_index) orelse return error.InvalidWickTerm;

    const event = Correlator.WickTermEvent{
        .left_index = left_index,
        .right_index = right_index,
        .term_index = term_index,
    };
    try sink.emitWickTermStart(event);

    var scalar_index: usize = 0;
    while (scalar_index < primitive.scalarCount()) : (scalar_index += 1) {
        try sink.emitWickScalar(primitive.scalar(scalar_index) orelse return error.InvalidWickFactor);
    }

    var coordinate_index: usize = 0;
    while (coordinate_index < primitive.coordinateCount()) : (coordinate_index += 1) {
        try sink.emitWickCoordinate(primitive.coordinate(coordinate_index) orelse return error.InvalidWickFactor);
    }

    var tensor_index: usize = 0;
    while (tensor_index < primitive.tensorCount()) : (tensor_index += 1) {
        try sink.emitWickTensor(primitive.tensor(tensor_index) orelse return error.InvalidWickFactor);
    }

    var action_index: usize = 0;
    while (action_index < primitive.actionCount()) : (action_index += 1) {
        try sink.emitWickAction(primitive.action(action_index) orelse return error.InvalidWickFactor);
    }

    var residual_index: usize = 0;
    while (residual_index < primitive.residualCount()) : (residual_index += 1) {
        try emitWickResidualOperator(pair, left_index, right_index, primitive.residual(residual_index) orelse return error.InvalidWickFactor, sink);
    }

    try sink.emitWickTermEnd();
}

fn wickPairTermPayloadFrom(rule_index: usize, term_index: usize, reversed: bool) !u64 {
    if (rule_index > std.math.maxInt(u32)) return error.TooManyWickRules;
    if (term_index > std.math.maxInt(u16)) return error.TooManyWickTerms;
    return @as(u64, @intCast(rule_index)) |
        (@as(u64, @intCast(term_index)) << 32) |
        (@as(u64, @intFromBool(reversed)) << 48);
}

fn wickPayloadRuleIndex(payload: u64) usize {
    return @intCast(payload & 0xffff_ffff);
}

fn wickPayloadTermIndex(payload: u64) usize {
    return @intCast((payload >> 32) & 0xffff);
}

fn wickPayloadReversed(payload: u64) bool {
    return ((payload >> 48) & 1) != 0;
}

fn actualSideIndex(pair: Correlator.WickPair, left_index: usize, right_index: usize, side: wick.Side) usize {
    return switch (side) {
        .left => if (pair.reversed) right_index else left_index,
        .right => if (pair.reversed) left_index else right_index,
    };
}

fn emitWickResidualOperator(pair: Correlator.WickPair, left_index: usize, right_index: usize, side: wick.Side, sink: anytype) !void {
    const SinkPtr = @TypeOf(sink);
    const sink_info = @typeInfo(SinkPtr);
    if (sink_info != .pointer) return;
    const Sink = sink_info.pointer.child;
    if (!@hasDecl(Sink, "emitWickResidualOperator")) return;

    const input_index = actualSideIndex(pair, left_index, right_index, side);
    const operator = switch (side) {
        .left => pair.sideOp(.left),
        .right => pair.sideOp(.right),
    };
    try sink.emitWickResidualOperator(Correlator.WickResidualRef{
        .input_index = input_index,
        .operator = operator,
    });
}

const cache_pair_direct_width = 16;
const cache_pair_hash_slots = cache_pair_direct_width * cache_pair_direct_width;
const no_cached_pair = std.math.maxInt(u16);

fn branchBudgetOperatorCount(comptime budget: BranchBudget) usize {
    return switch (budget) {
        .standard => 128,
    };
}

fn branchBudgetCacheTerms(comptime budget: BranchBudget) usize {
    return switch (budget) {
        .standard => 66,
    };
}

fn maxTermFactors(comptime rules: []const wick.Rule, comptime selector: enum { scalars, coordinates, tensors, actions, residuals }) usize {
    var result: usize = 0;
    for (rules) |rule| {
        for (rule.expr.terms) |term| {
            const count = switch (selector) {
                .scalars => term.scalars.len,
                .coordinates => term.coordinates.len,
                .tensors => term.tensors.len,
                .actions => term.actions.len,
                .residuals => term.residuals.len,
            };
            if (count > result) result = count;
        }
    }
    return result;
}

fn atLeastOne(value: usize) usize {
    return if (value == 0) 1 else value;
}

fn branchLimits(comptime input: CorrelatorConfigInput) BranchLimits {
    const max_operators = branchBudgetOperatorCount(input.branch_budget);
    if (max_operators > 128) @compileError("zero-mode consumption mask supports at most 128 residual operators");
    const max_terms = max_operators / 2;
    const max_cached_terms = branchBudgetCacheTerms(input.branch_budget);
    const scalar_terms = atLeastOne(maxTermFactors(input.wick_rules, .scalars));
    const coordinate_terms = atLeastOne(maxTermFactors(input.wick_rules, .coordinates));
    const tensor_terms = atLeastOne(maxTermFactors(input.wick_rules, .tensors));
    const action_terms = atLeastOne(maxTermFactors(input.wick_rules, .actions));
    const residual_terms = atLeastOne(maxTermFactors(input.wick_rules, .residuals));

    return .{
        .max_operators = max_operators,
        .max_zero_mode_residuals = max_operators,
        .max_zero_mode_items = max_operators,
        .max_terms = max_terms,
        .max_scalars = scalar_terms * max_terms,
        .max_coordinates = coordinate_terms * max_terms,
        .max_tensors = tensor_terms * max_terms,
        .max_actions = action_terms * max_terms,
        .max_residuals = residual_terms * max_terms,
        .max_cached_terms = max_cached_terms,
        .max_cached_scalars = scalar_terms * max_cached_terms,
        .max_cached_coordinates = coordinate_terms * max_cached_terms,
        .max_cached_tensors = tensor_terms * max_cached_terms,
        .max_cached_actions = action_terms * max_cached_terms,
        .max_cached_residuals = residual_terms * max_cached_terms,
    };
}

const AccumulatedWickTerm = struct {
    event: Correlator.WickTermEvent,
    cache_index: u16 = no_cached_pair,
    scalar_start: u16,
    scalar_count: u16 = 0,
    coordinate_start: u16,
    coordinate_count: u16 = 0,
    tensor_start: u16,
    tensor_count: u16 = 0,
    action_start: u16,
    action_count: u16 = 0,
    residual_start: u16,
    residual_count: u16 = 0,
};

const CachedPairKey = struct {
    left: u8,
    right: u8,
    payload: u64,
};

fn AccumulatedBranch(comptime limits: BranchLimits) type {
    return struct {
        const Self = @This();

        const Snapshot = struct {
            term_count: u16,
            scalar_count: u16,
            coordinate_count: u16,
            tensor_count: u16,
            action_count: u16,
            residual_count: u16,
            logical_scalar_count: u16,
            logical_coordinate_count: u16,
            logical_tensor_count: u16,
            logical_action_count: u16,
            logical_residual_count: u16,
        };

        terms: [limits.max_terms]AccumulatedWickTerm = undefined,
        term_count: u16 = 0,
        scalars: [limits.max_scalars]Correlator.ResolvedScalarFactor = undefined,
        scalar_count: u16 = 0,
        coordinates: [limits.max_coordinates]coefficient.CoordinateFactor = undefined,
        coordinate_count: u16 = 0,
        tensors: [limits.max_tensors]Correlator.ResolvedTensorFactor = undefined,
        tensor_count: u16 = 0,
        actions: [limits.max_actions]Correlator.ResolvedActionFactor = undefined,
        action_count: u16 = 0,
        residuals: [limits.max_residuals]Correlator.WickResidualRef = undefined,
        residual_count: u16 = 0,
        cache_keys: [limits.max_cached_terms]CachedPairKey = undefined,
        cache_pair_index: [cache_pair_hash_slots]u16 = [_]u16{no_cached_pair} ** cache_pair_hash_slots,
        cache_terms: [limits.max_cached_terms]AccumulatedWickTerm = undefined,
        cache_count: u16 = 0,
        cache_scalars: [limits.max_cached_scalars]Correlator.ResolvedScalarFactor = undefined,
        cache_scalar_count: u16 = 0,
        cache_coordinates: [limits.max_cached_coordinates]coefficient.CoordinateFactor = undefined,
        cache_coordinate_count: u16 = 0,
        cache_tensors: [limits.max_cached_tensors]Correlator.ResolvedTensorFactor = undefined,
        cache_tensor_count: u16 = 0,
        cache_actions: [limits.max_cached_actions]Correlator.ResolvedActionFactor = undefined,
        cache_action_count: u16 = 0,
        cache_residuals: [limits.max_cached_residuals]Correlator.WickResidualRef = undefined,
        cache_residual_count: u16 = 0,
        logical_scalar_count: u16 = 0,
        logical_coordinate_count: u16 = 0,
        logical_tensor_count: u16 = 0,
        logical_action_count: u16 = 0,
        logical_residual_count: u16 = 0,

        /// init constructs an empty branch factor accumulator.
        pub fn init() Self {
            return .{};
        }

        /// snapshot records current array lengths for backtracking.
        pub fn snapshot(self: *const Self) Snapshot {
            return .{
                .term_count = self.term_count,
                .scalar_count = self.scalar_count,
                .coordinate_count = self.coordinate_count,
                .tensor_count = self.tensor_count,
                .action_count = self.action_count,
                .residual_count = self.residual_count,
                .logical_scalar_count = self.logical_scalar_count,
                .logical_coordinate_count = self.logical_coordinate_count,
                .logical_tensor_count = self.logical_tensor_count,
                .logical_action_count = self.logical_action_count,
                .logical_residual_count = self.logical_residual_count,
            };
        }

        /// restore truncates accumulated factors to a previous snapshot.
        pub fn restore(self: *Self, saved: Snapshot) void {
            self.term_count = saved.term_count;
            self.scalar_count = saved.scalar_count;
            self.coordinate_count = saved.coordinate_count;
            self.tensor_count = saved.tensor_count;
            self.action_count = saved.action_count;
            self.residual_count = saved.residual_count;
            self.logical_scalar_count = saved.logical_scalar_count;
            self.logical_coordinate_count = saved.logical_coordinate_count;
            self.logical_tensor_count = saved.logical_tensor_count;
            self.logical_action_count = saved.logical_action_count;
            self.logical_residual_count = saved.logical_residual_count;
        }

        fn currentTerm(self: *Self) *AccumulatedWickTerm {
            return &self.terms[self.term_count - 1];
        }

        fn cachePairSlot(left: usize, right: usize) usize {
            if (left < cache_pair_direct_width and right < cache_pair_direct_width) {
                return left * cache_pair_direct_width + right;
            }
            return ((left * 131) ^ right) & (cache_pair_hash_slots - 1);
        }

        fn findCache(self: *const Self, left: usize, right: usize, payload: u64) ?u16 {
            const direct = self.cache_pair_index[cachePairSlot(left, right)];
            if (direct != no_cached_pair) {
                const key = self.cache_keys[direct];
                if (key.left == left and key.right == right and key.payload == payload) return direct;
            }

            var index: u16 = 0;
            while (index < self.cache_count) : (index += 1) {
                const key = self.cache_keys[index];
                if (key.left == left and key.right == right and key.payload == payload) return index;
            }
            return null;
        }

        fn appendCachedTerm(self: *Self, cache_index: u16) !void {
            if (self.term_count == self.terms.len) return error.TooManyAccumulatedWickTerms;
            const cached = self.cache_terms[cache_index];
            self.terms[self.term_count] = cached;
            self.terms[self.term_count].cache_index = cache_index;
            self.term_count += 1;
            self.logical_scalar_count += cached.scalar_count;
            self.logical_coordinate_count += cached.coordinate_count;
            self.logical_tensor_count += cached.tensor_count;
            self.logical_action_count += cached.action_count;
            self.logical_residual_count += cached.residual_count;
        }

        /// primitiveTermCount returns the number of primitive pair terms in this branch.
        pub fn primitiveTermCount(self: *const Self) usize {
            return self.term_count;
        }

        /// scalarFactorCount returns the number of scalar factors in this branch.
        pub fn scalarFactorCount(self: *const Self) usize {
            return self.logical_scalar_count;
        }

        /// coordinateFactorCount returns the number of coordinate factors in this branch.
        pub fn coordinateFactorCount(self: *const Self) usize {
            return self.logical_coordinate_count;
        }

        /// tensorFactorCount returns the number of tensor factors in this branch.
        pub fn tensorFactorCount(self: *const Self) usize {
            return self.logical_tensor_count;
        }

        /// actionFactorCount returns the number of action factors in this branch.
        pub fn actionFactorCount(self: *const Self) usize {
            return self.logical_action_count;
        }

        /// residualFactorCount returns the number of residual operator refs in this branch.
        pub fn residualFactorCount(self: *const Self) usize {
            return self.logical_residual_count;
        }

        /// pushPairTerm appends one cached or freshly resolved primitive pair term.
        pub fn pushPairTerm(branch: *Self, config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, payload: u64) !void {
            if (branch.findCache(left_index, right_index, payload)) |cache_index| {
                try branch.appendCachedTerm(cache_index);
                return;
            }

            if (branch.cache_count == branch.cache_terms.len) {
                try emitWickPairTermPayloadData(config_ptr, ops, left_index, right_index, payload, branch);
                return;
            }

            const cache_index = branch.cache_count;
            const CacheSink = struct {
                branch: *Self,
                cache_index: u16,

                fn current(self: *@This()) *AccumulatedWickTerm {
                    return &self.branch.cache_terms[self.cache_index];
                }

                pub fn emitWickTermStart(self: *@This(), event: Correlator.WickTermEvent) !void {
                    self.branch.cache_terms[self.cache_index] = .{
                        .event = event,
                        .scalar_start = self.branch.cache_scalar_count,
                        .coordinate_start = self.branch.cache_coordinate_count,
                        .tensor_start = self.branch.cache_tensor_count,
                        .action_start = self.branch.cache_action_count,
                        .residual_start = self.branch.cache_residual_count,
                    };
                }

                pub fn emitWickScalar(self: *@This(), factor: Correlator.ResolvedScalarFactor) !void {
                    if (self.branch.cache_scalar_count == self.branch.cache_scalars.len) return error.TooManyCachedScalars;
                    self.branch.cache_scalars[self.branch.cache_scalar_count] = factor;
                    self.branch.cache_scalar_count += 1;
                    self.current().scalar_count += 1;
                }

                pub fn emitWickCoordinate(self: *@This(), factor: coefficient.CoordinateFactor) !void {
                    if (self.branch.cache_coordinate_count == self.branch.cache_coordinates.len) return error.TooManyCachedCoordinates;
                    self.branch.cache_coordinates[self.branch.cache_coordinate_count] = factor;
                    self.branch.cache_coordinate_count += 1;
                    self.current().coordinate_count += 1;
                }

                pub fn emitWickTensor(self: *@This(), factor: Correlator.ResolvedTensorFactor) !void {
                    if (self.branch.cache_tensor_count == self.branch.cache_tensors.len) return error.TooManyCachedTensors;
                    self.branch.cache_tensors[self.branch.cache_tensor_count] = factor;
                    self.branch.cache_tensor_count += 1;
                    self.current().tensor_count += 1;
                }

                pub fn emitWickAction(self: *@This(), factor: Correlator.ResolvedActionFactor) !void {
                    if (self.branch.cache_action_count == self.branch.cache_actions.len) return error.TooManyCachedActions;
                    self.branch.cache_actions[self.branch.cache_action_count] = factor;
                    self.branch.cache_action_count += 1;
                    self.current().action_count += 1;
                }

                pub fn emitWickResidualOperator(self: *@This(), residual: Correlator.WickResidualRef) !void {
                    if (self.branch.cache_residual_count == self.branch.cache_residuals.len) return error.TooManyCachedResiduals;
                    self.branch.cache_residuals[self.branch.cache_residual_count] = residual;
                    self.branch.cache_residual_count += 1;
                    self.current().residual_count += 1;
                }

                pub fn emitWickTermEnd(_: *@This()) !void {}
            };

            var cache_sink = CacheSink{ .branch = branch, .cache_index = cache_index };
            try emitWickPairTermPayloadData(config_ptr, ops, left_index, right_index, payload, &cache_sink);
            branch.cache_keys[cache_index] = .{ .left = @intCast(left_index), .right = @intCast(right_index), .payload = payload };
            const direct_slot = cachePairSlot(left_index, right_index);
            if (branch.cache_pair_index[direct_slot] == no_cached_pair) branch.cache_pair_index[direct_slot] = cache_index;
            branch.cache_count += 1;
            try branch.appendCachedTerm(cache_index);
        }

        /// emitWickTermStart appends one primitive term boundary.
        pub fn emitWickTermStart(self: *Self, event: Correlator.WickTermEvent) !void {
            if (self.term_count == self.terms.len) return error.TooManyAccumulatedWickTerms;
            self.terms[self.term_count] = .{
                .event = event,
                .scalar_start = self.scalar_count,
                .coordinate_start = self.coordinate_count,
                .tensor_start = self.tensor_count,
                .action_start = self.action_count,
                .residual_start = self.residual_count,
            };
            self.term_count += 1;
        }

        /// emitWickScalar appends one scalar factor.
        pub fn emitWickScalar(self: *Self, factor: Correlator.ResolvedScalarFactor) !void {
            if (self.scalar_count == self.scalars.len) return error.TooManyAccumulatedScalars;
            self.scalars[self.scalar_count] = factor;
            self.scalar_count += 1;
            self.currentTerm().scalar_count += 1;
            self.logical_scalar_count += 1;
        }

        /// emitWickCoordinate appends one coordinate factor.
        pub fn emitWickCoordinate(self: *Self, factor: coefficient.CoordinateFactor) !void {
            if (self.coordinate_count == self.coordinates.len) return error.TooManyAccumulatedCoordinates;
            self.coordinates[self.coordinate_count] = factor;
            self.coordinate_count += 1;
            self.currentTerm().coordinate_count += 1;
            self.logical_coordinate_count += 1;
        }

        /// emitWickTensor appends one tensor factor.
        pub fn emitWickTensor(self: *Self, factor: Correlator.ResolvedTensorFactor) !void {
            if (self.tensor_count == self.tensors.len) return error.TooManyAccumulatedTensors;
            self.tensors[self.tensor_count] = factor;
            self.tensor_count += 1;
            self.currentTerm().tensor_count += 1;
            self.logical_tensor_count += 1;
        }

        /// emitWickAction appends one action factor.
        pub fn emitWickAction(self: *Self, factor: Correlator.ResolvedActionFactor) !void {
            if (self.action_count == self.actions.len) return error.TooManyAccumulatedActions;
            self.actions[self.action_count] = factor;
            self.action_count += 1;
            self.currentTerm().action_count += 1;
            self.logical_action_count += 1;
        }

        /// emitWickResidualOperator appends one residual operator reference.
        pub fn emitWickResidualOperator(self: *Self, residual: Correlator.WickResidualRef) !void {
            if (self.residual_count == self.residuals.len) return error.TooManyAccumulatedResiduals;
            self.residuals[self.residual_count] = residual;
            self.residual_count += 1;
            self.currentTerm().residual_count += 1;
            self.logical_residual_count += 1;
        }

        /// emitWickTermEnd accepts the primitive term boundary.
        pub fn emitWickTermEnd(_: *Self) !void {}

        /// emit streams all accumulated primitive terms to the final sink.
        pub fn emit(self: *const Self, sink: anytype) !void {
            const SinkPtr = @TypeOf(sink);
            const sink_info = @typeInfo(SinkPtr);
            if (sink_info == .pointer and @hasDecl(sink_info.pointer.child, "emitWickBranchTerm")) {
                try sink.emitWickBranchTerm(self);
                return;
            }

            const emit_residuals = sink_info == .pointer and @hasDecl(sink_info.pointer.child, "emitWickResidualOperator");
            const replay_actions = self.logical_action_count != 0;
            const replay_residuals = emit_residuals and self.logical_residual_count != 0;

            var term_index: usize = 0;
            while (term_index < self.term_count) : (term_index += 1) {
                const term = self.terms[term_index];
                const source_term = if (term.cache_index == no_cached_pair) term else self.cache_terms[term.cache_index];
                try sink.emitWickTermStart(term.event);

                var scalar_index: usize = 0;
                while (scalar_index < term.scalar_count) : (scalar_index += 1) {
                    if (term.cache_index == no_cached_pair) {
                        try sink.emitWickScalar(self.scalars[source_term.scalar_start + scalar_index]);
                    } else {
                        try sink.emitWickScalar(self.cache_scalars[source_term.scalar_start + scalar_index]);
                    }
                }

                var coordinate_index: usize = 0;
                while (coordinate_index < term.coordinate_count) : (coordinate_index += 1) {
                    if (term.cache_index == no_cached_pair) {
                        try sink.emitWickCoordinate(self.coordinates[source_term.coordinate_start + coordinate_index]);
                    } else {
                        try sink.emitWickCoordinate(self.cache_coordinates[source_term.coordinate_start + coordinate_index]);
                    }
                }

                var tensor_index: usize = 0;
                while (tensor_index < term.tensor_count) : (tensor_index += 1) {
                    if (term.cache_index == no_cached_pair) {
                        try sink.emitWickTensor(self.tensors[source_term.tensor_start + tensor_index]);
                    } else {
                        try sink.emitWickTensor(self.cache_tensors[source_term.tensor_start + tensor_index]);
                    }
                }

                if (replay_actions) {
                    var action_index: usize = 0;
                    while (action_index < term.action_count) : (action_index += 1) {
                        if (term.cache_index == no_cached_pair) {
                            try sink.emitWickAction(self.actions[source_term.action_start + action_index]);
                        } else {
                            try sink.emitWickAction(self.cache_actions[source_term.action_start + action_index]);
                        }
                    }
                }

                if (replay_residuals) {
                    var residual_index: usize = 0;
                    while (residual_index < term.residual_count) : (residual_index += 1) {
                        if (term.cache_index == no_cached_pair) {
                            try sink.emitWickResidualOperator(self.residuals[source_term.residual_start + residual_index]);
                        } else {
                            try sink.emitWickResidualOperator(self.cache_residuals[source_term.residual_start + residual_index]);
                        }
                    }
                }

                try sink.emitWickTermEnd();
            }
        }
    };
}

fn matchIndexedWickPairTerm(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, left: kernel.Call.LocalOp, right: kernel.Call.LocalOp, term_ordinal: usize) !?Correlator.MatchedWickTerm {
    const key = wickRuleKey(left.kind, right.kind);
    var entry_index = lowerBoundPairLookup(config_ptr.pair_lookup, key);
    var remaining = term_ordinal;

    while (entry_index < config_ptr.pair_lookup.len and config_ptr.pair_lookup[entry_index].key == key) : (entry_index += 1) {
        const entry = config_ptr.pair_lookup[entry_index];
        const rule_index: usize = @intCast(entry.rule_index);
        if (rule_index >= config_ptr.wick_rules.len) return error.InvalidPairLookup;
        const rule = &config_ptr.wick_rules[rule_index];
        if (remaining < rule.expr.terms.len) {
            return .{ .pair = .{
                .rule = rule,
                .config = config_ptr,
                .left = left,
                .right = right,
                .labels = ops.labels,
                .reversed = entry.reversed,
            }, .rule_index = rule_index, .term_index = remaining };
        }
        remaining -= rule.expr.terms.len;
    }

    _ = left_index;
    _ = right_index;
    return null;
}

fn matchScannedWickPairTerm(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, left: kernel.Call.LocalOp, right: kernel.Call.LocalOp, term_ordinal: usize) ?Correlator.MatchedWickTerm {
    var remaining = term_ordinal;

    for (config_ptr.wick_rules, 0..) |*rule, rule_index| {
        if (matchRule(config_ptr, rule, left, right, ops.labels)) |pair| {
            if (remaining < pair.rule.expr.terms.len) {
                return .{ .pair = pair, .rule_index = rule_index, .term_index = remaining };
            }
            remaining -= pair.rule.expr.terms.len;
        }
    }

    _ = left_index;
    _ = right_index;
    return null;
}

fn matchWickPairTerm(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, term_ordinal: usize) !?Correlator.MatchedWickTerm {
    if (left_index >= ops.operators.len or right_index >= ops.operators.len or left_index == right_index) return error.InvalidOperatorIndex;

    const left = ops.operators[left_index];
    const right = ops.operators[right_index];
    if (config_ptr.pair_lookup.len != 0) {
        return matchIndexedWickPairTerm(config_ptr, ops, left_index, right_index, left, right, term_ordinal);
    }

    return matchScannedWickPairTerm(config_ptr, ops, left_index, right_index, left, right, term_ordinal);
}

fn emitIndexedWickPairTerms(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, left: kernel.Call.LocalOp, right: kernel.Call.LocalOp, sink: anytype) !usize {
    const key = wickRuleKey(left.kind, right.kind);
    var entry_index = lowerBoundPairLookup(config_ptr.pair_lookup, key);
    var emitted: usize = 0;

    while (entry_index < config_ptr.pair_lookup.len and config_ptr.pair_lookup[entry_index].key == key) : (entry_index += 1) {
        const entry = config_ptr.pair_lookup[entry_index];
        const rule_index: usize = @intCast(entry.rule_index);
        if (rule_index >= config_ptr.wick_rules.len) return error.InvalidPairLookup;
        const rule = &config_ptr.wick_rules[rule_index];
        const pair = Correlator.WickPair{
            .rule = rule,
            .config = config_ptr,
            .left = left,
            .right = right,
            .labels = ops.labels,
            .reversed = entry.reversed,
        };

        var term_index: usize = 0;
        while (term_index < pair.rule.expr.terms.len) : (term_index += 1) {
            try emitPrimitiveWickTerm(pair, left_index, right_index, term_index, sink);
            emitted += 1;
        }
    }

    return emitted;
}

fn emitScannedWickPairTerms(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, left: kernel.Call.LocalOp, right: kernel.Call.LocalOp, sink: anytype) !usize {
    var emitted: usize = 0;

    for (config_ptr.wick_rules) |*rule| {
        if (matchRule(config_ptr, rule, left, right, ops.labels)) |pair| {
            var term_index: usize = 0;
            while (term_index < pair.rule.expr.terms.len) : (term_index += 1) {
                try emitPrimitiveWickTerm(pair, left_index, right_index, term_index, sink);
                emitted += 1;
            }
        }
    }

    return emitted;
}

fn countIndexedWickPairTerms(config_ptr: *const CorrelatorConfigData, left: kernel.Call.LocalOp, right: kernel.Call.LocalOp) !usize {
    const key = wickRuleKey(left.kind, right.kind);
    var entry_index = lowerBoundPairLookup(config_ptr.pair_lookup, key);
    var count: usize = 0;

    while (entry_index < config_ptr.pair_lookup.len and config_ptr.pair_lookup[entry_index].key == key) : (entry_index += 1) {
        const rule_index: usize = @intCast(config_ptr.pair_lookup[entry_index].rule_index);
        if (rule_index >= config_ptr.wick_rules.len) return error.InvalidPairLookup;
        count += config_ptr.wick_rules[rule_index].expr.terms.len;
    }

    return count;
}

fn countScannedWickPairTerms(config_ptr: *const CorrelatorConfigData, left: kernel.Call.LocalOp, right: kernel.Call.LocalOp) usize {
    var count: usize = 0;
    for (config_ptr.wick_rules) |rule| {
        if (ruleMatches(rule, left, right) != null) count += rule.expr.terms.len;
    }
    return count;
}

/// countWickPairTerms counts primitive terms for two input positions without resolving factors.
fn countWickPairTermsData(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize) !usize {
    if (left_index >= ops.operators.len or right_index >= ops.operators.len or left_index == right_index) return error.InvalidOperatorIndex;

    const left = ops.operators[left_index];
    const right = ops.operators[right_index];
    if (config_ptr.pair_lookup.len != 0) {
        return countIndexedWickPairTerms(config_ptr, left, right);
    }

    return countScannedWickPairTerms(config_ptr, left, right);
}

fn emitWickPairTermsData(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, sink: anytype) !usize {
    if (left_index >= ops.operators.len or right_index >= ops.operators.len or left_index == right_index) return error.InvalidOperatorIndex;

    const left = ops.operators[left_index];
    const right = ops.operators[right_index];
    if (config_ptr.pair_lookup.len != 0) {
        return emitIndexedWickPairTerms(config_ptr, ops, left_index, right_index, left, right, sink);
    }

    return emitScannedWickPairTerms(config_ptr, ops, left_index, right_index, left, right, sink);
}

fn emitWickPairTermData(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, term_ordinal: usize, sink: anytype) !void {
    const matched = try matchWickPairTerm(config_ptr, ops, left_index, right_index, term_ordinal) orelse return error.InvalidWickTerm;
    try emitPrimitiveWickTerm(matched.pair, left_index, right_index, matched.term_index, sink);
}

fn wickPairTermPayloadData(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, term_ordinal: usize) !u64 {
    const matched = try matchWickPairTerm(config_ptr, ops, left_index, right_index, term_ordinal) orelse return error.InvalidWickTerm;
    return wickPairTermPayloadFrom(matched.rule_index, matched.term_index, matched.pair.reversed);
}

fn wickPairTermInfoData(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, term_ordinal: usize, residuals: *[2]usize, payload: *u64, residual_count: *usize) !void {
    const matched = try matchWickPairTerm(config_ptr, ops, left_index, right_index, term_ordinal) orelse return error.InvalidWickTerm;
    const source = matched.pair.rule.expr.terms[matched.term_index].residuals;
    if (source.len > residuals.len) return error.TooManyWickTermResiduals;
    for (source, 0..) |side, index| {
        residuals[index] = actualSideIndex(matched.pair, left_index, right_index, side);
    }
    payload.* = try wickPairTermPayloadFrom(matched.rule_index, matched.term_index, matched.pair.reversed);
    residual_count.* = source.len;
}

fn emitWickPairTermPayloadData(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, payload: u64, sink: anytype) !void {
    const rule_index = wickPayloadRuleIndex(payload);
    if (rule_index >= config_ptr.wick_rules.len) return error.InvalidWickTerm;
    const pair = Correlator.WickPair{
        .rule = &config_ptr.wick_rules[rule_index],
        .config = config_ptr,
        .left = ops.operators[left_index],
        .right = ops.operators[right_index],
        .labels = ops.labels,
        .reversed = wickPayloadReversed(payload),
    };
    try emitPrimitiveWickTerm(pair, left_index, right_index, wickPayloadTermIndex(payload), sink);
}

fn wickPairTermResidualsData(config_ptr: *const CorrelatorConfigData, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, term_ordinal: usize, residuals: *[2]usize) !usize {
    const matched = try matchWickPairTerm(config_ptr, ops, left_index, right_index, term_ordinal) orelse return error.InvalidWickTerm;
    const source = matched.pair.rule.expr.terms[matched.term_index].residuals;
    if (source.len > residuals.len) return error.TooManyWickTermResiduals;
    for (source, 0..) |side, index| {
        residuals[index] = actualSideIndex(matched.pair, left_index, right_index, side);
    }
    return source.len;
}

fn RuntimeWickTactic(comptime ConfigHandle: type) type {
    return struct {
        /// Config is the shared preset runtime correlator config.
        pub const Config = CorrelatorConfigData;
        const traversal_operator_count = ConfigHandle.branch_limits.max_operators;
        /// BranchState accumulates resolved Wick factors along one DFS branch.
        pub const BranchState = AccumulatedBranch(ConfigHandle.branch_limits);

        /// emitPairTerms adapts original occurrence pairs to the primitive Wick emitter.
        pub fn emitPairTerms(config_ptr: *const Config, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, sink: anytype) !usize {
            return emitWickPairTermsData(config_ptr, ops, left_index, right_index, sink);
        }

        /// emitPairTerm emits one selected primitive Wick term.
        pub fn emitPairTerm(config_ptr: *const Config, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, term_ordinal: usize, sink: anytype) !void {
            return emitWickPairTermData(config_ptr, ops, left_index, right_index, term_ordinal, sink);
        }

        /// pairTermCount counts primitive pair terms without emitting factors.
        pub fn pairTermCount(config_ptr: *const Config, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize) !usize {
            return countWickPairTermsData(config_ptr, ops, left_index, right_index);
        }

        /// pairTermResiduals returns original residual occurrences for one primitive term.
        pub fn pairTermResiduals(config_ptr: *const Config, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, term_ordinal: usize, residuals: *[2]usize) !usize {
            return wickPairTermResidualsData(config_ptr, ops, left_index, right_index, term_ordinal, residuals);
        }

        /// pairTermPayload returns cached rule payload for a primitive pair term.
        pub fn pairTermPayload(config_ptr: *const Config, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, term_ordinal: usize) !u64 {
            return wickPairTermPayloadData(config_ptr, ops, left_index, right_index, term_ordinal);
        }

        /// pairTermInfo returns residual occurrences and cached replay payload from one pair match.
        pub fn pairTermInfo(config_ptr: *const Config, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, term_ordinal: usize, residuals: *[2]usize, payload: *u64, residual_count: *usize) !void {
            return wickPairTermInfoData(config_ptr, ops, left_index, right_index, term_ordinal, residuals, payload, residual_count);
        }

        /// emitPairTermPayload replays one primitive term without matching rules again.
        pub fn emitPairTermPayload(config_ptr: *const Config, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, payload: u64, sink: anytype) !void {
            return emitWickPairTermPayloadData(config_ptr, ops, left_index, right_index, payload, sink);
        }

        /// pushBranchPairTerm appends one primitive pair term to a branch accumulator.
        pub fn pushBranchPairTerm(config_ptr: *const Config, ops: kernel.Call.MultiOp, left_index: usize, right_index: usize, payload: u64, branch: *BranchState) !void {
            return branch.pushPairTerm(config_ptr, ops, left_index, right_index, payload);
        }

        /// emitAccumulatedBranch streams cached pair factors followed by the zero-mode base case.
        pub fn emitAccumulatedBranch(config_ptr: *const Config, ops: kernel.Call.MultiOp, branch: *const BranchState, sign: i8, residual_indices: []const usize, sink: anytype) !void {
            if (sign < 0) {
                try emitBranchSign(config_ptr, sign, sink);
            }
            try branch.emit(sink);
            try generatedTrustedZeroModeBaseCase(ConfigHandle, config_ptr, ops, residual_indices, sink);
        }

        /// emitFullContractionBranch streams a full Wick branch with the empty base case.
        pub fn emitFullContractionBranch(config_ptr: *const Config, ops: kernel.Call.MultiOp, branch: *const BranchState, sign: i8, sink: anytype) !void {
            if (sign < 0) {
                try emitBranchSign(config_ptr, sign, sink);
            }
            try branch.emit(sink);
            _ = ops;
            try generatedEmptyZeroModeBaseCase(ConfigHandle, config_ptr, sink);
        }

        /// operatorParity returns true for configured fermionic operator kinds.
        pub fn operatorParity(config_ptr: *const Config, ops: kernel.Call.MultiOp, index: usize) bool {
            const kind = ops.operators[index].kind;
            return kindIn(kind, config_ptr.fermion_kinds);
        }

        /// operatorCanRemainInZeroMode returns true when a residual can be consumed by zero modes.
        pub fn operatorCanRemainInZeroMode(config_ptr: *const Config, ops: kernel.Call.MultiOp, index: usize) bool {
            _ = config_ptr;
            return generatedZeroModeCanConsumeKind(ConfigHandle, ops.operators[index].kind);
        }

        /// emitBranchSign forwards an accumulated fermion sign when the sink accepts it.
        pub fn emitBranchSign(_: *const Config, sign: i8, sink: anytype) !void {
            const SinkPtr = @TypeOf(sink);
            const sink_info = @typeInfo(SinkPtr);
            if (sink_info != .pointer) return;
            const Sink = sink_info.pointer.child;
            if (@hasDecl(Sink, "emitWickBranchSign")) {
                try sink.emitWickBranchSign(sign);
            }
        }

        /// emitZeroModeBaseCase adapts residual original occurrences to the zero-mode evaluator.
        pub fn emitZeroModeBaseCase(config_ptr: *const Config, ops: kernel.Call.MultiOp, residual_indices: []const usize, sink: anytype) !bool {
            return generatedZeroModeBaseCase(ConfigHandle, config_ptr, ops, residual_indices, sink);
        }

        /// zeroModeBaseCaseSucceeds tests base-case viability without emitting factors.
        pub fn zeroModeBaseCaseSucceeds(config_ptr: *const Config, ops: kernel.Call.MultiOp, residual_indices: []const usize) !bool {
            return generatedZeroModeBaseCaseSucceeds(ConfigHandle, config_ptr, ops, residual_indices);
        }
    };
}

fn operatorListData(ops: anytype) KernelOperatorList {
    const Ops = @TypeOf(ops);
    if (Ops == KernelOperatorList) return ops;
    return switch (@typeInfo(Ops)) {
        .pointer => |ptr| if (ptr.child == OperatorList) blk: {
            const state: *const LocalStateImpl = @ptrCast(@alignCast(ops));
            break :blk .{ .operators = state.owned_operators, .labels = &state.label_store };
        } else {
            @compileError("correlator operators must come from local.ops");
        },
        else => @compileError("correlator operators must come from local.ops"),
    };
}

/// streamCorrelator evaluates Wick branches and streams accepted base cases.
pub fn streamCorrelator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
    const Ptr = @TypeOf(config_ptr);
    const ptr_info = @typeInfo(Ptr);
    if (ptr_info != .pointer) @compileError("correlator config must be passed by pointer");
    const ConfigHandle = ptr_info.pointer.child;
    const data = configData(config_ptr);
    return wick_correlator.wickCorrelator(RuntimeWickTactic(ConfigHandle), data, operatorListData(ops), sink);
}
