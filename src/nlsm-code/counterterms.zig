const std = @import("std");
const geometry = @import("local_geometry_reducer.zig");
const scheme = @import("scheme.zig");

/// Rational stores one compact exact coefficient.
pub const Rational = struct {
    numerator: i64 = 0,
    denominator: u32 = 1,

    /// normalized returns the coefficient in reduced form with a positive denominator.
    pub fn normalized(self: Rational) Rational {
        std.debug.assert(self.denominator != 0);
        if (self.numerator == 0) return .{};

        const abs_num: u64 = @intCast(if (self.numerator < 0) -self.numerator else self.numerator);
        const gcd = std.math.gcd(abs_num, self.denominator);
        return .{
            .numerator = @divExact(self.numerator, @as(i64, @intCast(gcd))),
            .denominator = @divExact(self.denominator, @as(u32, @intCast(gcd))),
        };
    }

    /// add combines two exact coefficients.
    pub fn add(left: Rational, right: Rational) !Rational {
        const lhs = try std.math.mul(i64, left.numerator, right.denominator);
        const rhs = try std.math.mul(i64, right.numerator, left.denominator);
        const numerator = try std.math.add(i64, lhs, rhs);
        const denominator = try std.math.mul(u32, left.denominator, right.denominator);
        return (Rational{ .numerator = numerator, .denominator = denominator }).normalized();
    }

    /// mul multiplies two exact coefficients.
    pub fn mul(left: Rational, right: Rational) !Rational {
        return (Rational{
            .numerator = try std.math.mul(i64, left.numerator, right.numerator),
            .denominator = try std.math.mul(u32, left.denominator, right.denominator),
        }).normalized();
    }

    /// scale multiplies one coefficient by a small signed integer.
    pub fn scale(self: Rational, factor: i64) !Rational {
        return (Rational{
            .numerator = try std.math.mul(i64, self.numerator, factor),
            .denominator = self.denominator,
        }).normalized();
    }
};

/// LocalCountertermKind names the local operator basis used by renormalization.
pub const LocalCountertermKind = enum(u8) {
    metric_beta,
    b_field_beta,
    dilaton_beta,
    kahler_potential_beta,
    scalar_effective_action,
};

/// KernelFamily identifies one regulated loop-integral family.
pub const KernelFamily = enum(u8) {
    bubble,
    nested_bubble,
    sunset,
    ladder,
    vacuum,
    scaleless_tadpole,
};

/// KernelSignature stores the reduced loop-kernel descriptor emitted by one branch.
pub const KernelSignature = struct {
    family: KernelFamily,
    loop_order: u8,
    vertex_count: u8 = 0,
    pair_count: u8 = 0,
    background_d_x0: u8 = 0,
    background_dbar_x0: u8 = 0,
    propagator_len: u8 = 0,
    propagator_powers: [8]u8 = [_]u8{0} ** 8,
    primitive_pair_histogram: [8]u8 = [_]u8{0} ** 8,
    left_fermion_derivative_order_total: u16 = 0,
    right_fermion_derivative_order_total: u16 = 0,
    numerator_rank: u8 = 0,
    external_derivative_order: u8 = 0,

    /// isScaleless reports whether dimensional regularization kills the family outright.
    pub fn isScaleless(self: KernelSignature) bool {
        return self.family == .scaleless_tadpole;
    }
};

/// PoleRow is one local pole term emitted after loop-kernel evaluation.
pub const PoleRow = struct {
    scheme: scheme.DimRegMS,
    local_operator: LocalCountertermKind,
    target_flavor: geometry.GeometryFlavor = .generic_riemannian,
    loop_order: u8,
    pole_order: u8,
    alpha_prime_power: i16 = 0,
    residue: Rational,
    kernel: KernelSignature,
    term: geometry.TensorTerm,
};

/// BetaRow is one assembled simple-pole contribution in the operator basis.
pub const BetaRow = struct {
    scheme: scheme.DimRegMS,
    local_operator: LocalCountertermKind,
    target_flavor: geometry.GeometryFlavor = .generic_riemannian,
    loop_order: u8,
    alpha_prime_power: i16 = 0,
    coefficient: Rational,
    term: geometry.TensorTerm,
    source_simple_pole_count: u16 = 0,
};

fn sameSlot(left: geometry.TensorSlot, right: geometry.TensorSlot) bool {
    return left.id == right.id and left.sort == right.sort and left.variance == right.variance;
}

fn sameSlots(left: []const geometry.TensorSlot, right: []const geometry.TensorSlot) bool {
    if (left.len != right.len) return false;
    for (left, right) |lhs, rhs| if (!sameSlot(lhs, rhs)) return false;
    return true;
}

fn sameAtom(left: geometry.TensorAtom, right: geometry.TensorAtom) bool {
    return left.kind == right.kind and sameSlots(left.slots, right.slots) and sameSlots(left.derivative_slots, right.derivative_slots);
}

/// sameTensorTermIgnoreCoefficient reports structural equality of local tensor monomials.
pub fn sameTensorTermIgnoreCoefficient(left: geometry.TensorTerm, right: geometry.TensorTerm) bool {
    if (left.atoms.len != right.atoms.len) return false;
    for (left.atoms, right.atoms) |lhs, rhs| if (!sameAtom(lhs, rhs)) return false;
    return true;
}

/// normalizedContribution combines one analytic pole residue with the tensor-row integer coefficient.
pub fn normalizedContribution(row: PoleRow) !Rational {
    return row.residue.scale(row.term.coefficient);
}

test "rational addition and scaling stay reduced" {
    const testing = std.testing;
    try testing.expectEqual(Rational{ .numerator = 5, .denominator = 6 }, try (Rational{ .numerator = 1, .denominator = 2 }).add(.{ .numerator = 1, .denominator = 3 }));
    try testing.expectEqual(Rational{ .numerator = -3, .denominator = 2 }, try (Rational{ .numerator = 3, .denominator = 4 }).scale(-2));
    try testing.expectEqual(Rational{ .numerator = 2, .denominator = 9 }, try (Rational{ .numerator = 1, .denominator = 3 }).mul(.{ .numerator = 2, .denominator = 3 }));
}

test "tensor-term equality ignores row coefficient but respects slots" {
    const testing = std.testing;
    const slots = [_]geometry.TensorSlot{
        .{ .id = 1, .sort = .real_tangent },
        .{ .id = 2, .sort = .real_tangent },
        .{ .id = 3, .sort = .real_tangent },
        .{ .id = 4, .sort = .real_tangent },
    };
    const atoms = [_]geometry.TensorAtom{.{ .kind = .riemann, .slots = &slots }};
    try testing.expect(sameTensorTermIgnoreCoefficient(.{ .coefficient = 2, .atoms = &atoms }, .{ .coefficient = -9, .atoms = &atoms }));
}
