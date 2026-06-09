const std = @import("std");

/// GeometryFlavor selects the target-geometry quotient used by local reducers.
pub const GeometryFlavor = enum(u8) {
    generic_riemannian,
    kahler,
    calabi_yau,
    hyperkahler,

    fn isKahler(self: GeometryFlavor) bool {
        return switch (self) {
            .generic_riemannian => false,
            .kahler, .calabi_yau, .hyperkahler => true,
        };
    }

    fn isRicciFlat(self: GeometryFlavor) bool {
        return switch (self) {
            .calabi_yau, .hyperkahler => true,
            .generic_riemannian, .kahler => false,
        };
    }
};

/// TensorSlotSort classifies a target tensor slot by complex type and variance.
pub const TensorSlotSort = enum(u8) {
    real_tangent,
    holomorphic_tangent,
    antiholomorphic_tangent,
    real_cotangent,
    holomorphic_cotangent,
    antiholomorphic_cotangent,
};

/// targetU1Charge returns the target holomorphic-degree charge of one slot.
pub fn targetU1Charge(sort: TensorSlotSort) i8 {
    return switch (sort) {
        .real_tangent, .real_cotangent => 0,
        .holomorphic_tangent, .holomorphic_cotangent => 1,
        .antiholomorphic_tangent, .antiholomorphic_cotangent => -1,
    };
}

const ComplexSort = enum(u2) { real, holomorphic, antiholomorphic };

fn complexSort(sort: TensorSlotSort) ComplexSort {
    return switch (sort) {
        .real_tangent, .real_cotangent => .real,
        .holomorphic_tangent, .holomorphic_cotangent => .holomorphic,
        .antiholomorphic_tangent, .antiholomorphic_cotangent => .antiholomorphic,
    };
}

fn conjugateComplexSort(left: TensorSlotSort, right: TensorSlotSort) bool {
    return switch (complexSort(left)) {
        .real => complexSort(right) == .real,
        .holomorphic => complexSort(right) == .antiholomorphic,
        .antiholomorphic => complexSort(right) == .holomorphic,
    };
}

/// Variance records whether a tensor slot is upper or lower.
pub const Variance = enum(u8) { lower, upper };

/// TensorSlot is one compact target-index occurrence in a local tensor atom.
pub const TensorSlot = struct {
    id: u32,
    sort: TensorSlotSort,
    variance: Variance = .lower,
};

/// TensorAtomKind identifies one local geometry tensor atom.
pub const TensorAtomKind = enum(u8) {
    metric,
    hermitian_metric,
    riemann,
    ricci,
    scalar_curvature,
    covariant_derivative,
};

/// TensorAtom is one local geometry tensor row.
pub const TensorAtom = struct {
    kind: TensorAtomKind,
    slots: []const TensorSlot = &.{},
    derivative_slots: []const TensorSlot = &.{},
};

/// TensorTerm is a streamed product of local geometry atoms.
pub const TensorTerm = struct {
    coefficient: i64 = 1,
    atoms: []const TensorAtom = &.{},
};

/// ReductionOptions selects the local quotient checks applied to one term.
pub const ReductionOptions = struct {
    flavor: GeometryFlavor = .generic_riemannian,
    require_neutral_target_charge: bool = false,
};

/// ReductionSummary reports the reducer decision without materializing a sum.
pub const ReductionSummary = struct {
    coefficient: i64 = 1,
    atom_count: usize = 0,
    target_charge: i16 = 0,
    zero: bool = false,
    dropped_ricci_flat_atom_count: u16 = 0,
    non_neutral: bool = false,
};

fn validateAtom(atom: TensorAtom) !void {
    switch (atom.kind) {
        .metric, .hermitian_metric, .ricci => if (atom.slots.len != 2 or atom.derivative_slots.len != 0) return error.InvalidTensorAtom,
        .riemann => if (atom.slots.len != 4 or atom.derivative_slots.len != 0) return error.InvalidTensorAtom,
        .scalar_curvature => if (atom.slots.len != 0 or atom.derivative_slots.len != 0) return error.InvalidTensorAtom,
        .covariant_derivative => if (atom.derivative_slots.len == 0) return error.InvalidTensorAtom,
    }
}

fn addCharge(charge: *i16, slots: []const TensorSlot) void {
    for (slots) |slot| charge.* += targetU1Charge(slot.sort);
}

fn kahlerRiemannTypeAllowed(slots: []const TensorSlot) bool {
    var holomorphic_count: u8 = 0;
    var antiholomorphic_count: u8 = 0;
    for (slots) |slot| switch (complexSort(slot.sort)) {
        .real => return false,
        .holomorphic => holomorphic_count += 1,
        .antiholomorphic => antiholomorphic_count += 1,
    };
    return holomorphic_count == 2 and antiholomorphic_count == 2;
}

fn atomVanishes(options: ReductionOptions, atom: TensorAtom, summary: *ReductionSummary) bool {
    if (options.flavor.isRicciFlat()) {
        switch (atom.kind) {
            .ricci, .scalar_curvature => {
                summary.dropped_ricci_flat_atom_count += 1;
                return true;
            },
            else => {},
        }
    }

    if (options.flavor.isKahler()) {
        switch (atom.kind) {
            .hermitian_metric => return !conjugateComplexSort(atom.slots[0].sort, atom.slots[1].sort),
            .riemann => return !kahlerRiemannTypeAllowed(atom.slots),
            .ricci => return !conjugateComplexSort(atom.slots[0].sort, atom.slots[1].sort),
            else => {},
        }
    }

    return false;
}

/// reduceLocalTerm filters one streamed local geometry term into caller storage.
pub fn reduceLocalTerm(term: TensorTerm, options: ReductionOptions, output: []TensorAtom) !ReductionSummary {
    var summary = ReductionSummary{ .coefficient = term.coefficient };

    for (term.atoms) |atom| {
        try validateAtom(atom);
        addCharge(&summary.target_charge, atom.slots);
        addCharge(&summary.target_charge, atom.derivative_slots);

        if (atomVanishes(options, atom, &summary)) {
            summary.zero = true;
            summary.atom_count = 0;
            return summary;
        }

        if (summary.atom_count == output.len) return error.OutputTooSmall;
        output[summary.atom_count] = atom;
        summary.atom_count += 1;
    }

    if (options.require_neutral_target_charge and summary.target_charge != 0) {
        summary.zero = true;
        summary.non_neutral = true;
        summary.atom_count = 0;
    }

    return summary;
}

test "calabi-yau reducer drops ricci-flat local terms" {
    const testing = std.testing;
    const slots = [_]TensorSlot{
        .{ .id = 1, .sort = .holomorphic_tangent },
        .{ .id = 2, .sort = .antiholomorphic_tangent },
    };
    const atoms = [_]TensorAtom{.{ .kind = .ricci, .slots = &slots }};
    var output: [1]TensorAtom = undefined;

    const summary = try reduceLocalTerm(.{ .atoms = &atoms }, .{ .flavor = .calabi_yau }, &output);
    try testing.expect(summary.zero);
    try testing.expectEqual(@as(u16, 1), summary.dropped_ricci_flat_atom_count);
    try testing.expectEqual(@as(usize, 0), summary.atom_count);
}

test "kahler reducer filters same-type curvature but keeps mixed type" {
    const testing = std.testing;
    const bad_slots = [_]TensorSlot{
        .{ .id = 1, .sort = .holomorphic_tangent },
        .{ .id = 2, .sort = .holomorphic_tangent },
        .{ .id = 3, .sort = .holomorphic_tangent },
        .{ .id = 4, .sort = .holomorphic_tangent },
    };
    const bad_atoms = [_]TensorAtom{.{ .kind = .riemann, .slots = &bad_slots }};
    var bad_output: [1]TensorAtom = undefined;
    try testing.expect((try reduceLocalTerm(.{ .atoms = &bad_atoms }, .{ .flavor = .kahler }, &bad_output)).zero);

    const good_slots = [_]TensorSlot{
        .{ .id = 1, .sort = .holomorphic_tangent },
        .{ .id = 2, .sort = .antiholomorphic_tangent },
        .{ .id = 3, .sort = .holomorphic_tangent },
        .{ .id = 4, .sort = .antiholomorphic_tangent },
    };
    const good_atoms = [_]TensorAtom{.{ .kind = .riemann, .slots = &good_slots }};
    var good_output: [1]TensorAtom = undefined;
    const summary = try reduceLocalTerm(.{ .atoms = &good_atoms }, .{ .flavor = .kahler, .require_neutral_target_charge = true }, &good_output);
    try testing.expect(!summary.zero);
    try testing.expectEqual(@as(i16, 0), summary.target_charge);
    try testing.expectEqual(@as(usize, 1), summary.atom_count);
}

test "target charge neutrality filters charged local terms" {
    const testing = std.testing;
    const derivative_slots = [_]TensorSlot{.{ .id = 1, .sort = .holomorphic_tangent }};
    const atoms = [_]TensorAtom{.{ .kind = .covariant_derivative, .derivative_slots = &derivative_slots }};
    var output: [1]TensorAtom = undefined;

    const summary = try reduceLocalTerm(.{ .atoms = &atoms }, .{ .require_neutral_target_charge = true }, &output);
    try testing.expect(summary.zero);
    try testing.expect(summary.non_neutral);
    try testing.expectEqual(@as(i16, 1), summary.target_charge);
}
