/// DerivativeProfile records the local worldsheet derivative content of one free field.
pub const DerivativeProfile = packed struct(u8) {
    holomorphic: u4 = 0,
    antiholomorphic: u4 = 0,
};

/// BosonSpherePairKernel names one primitive free-boson sphere pair kernel.
pub const BosonSpherePairKernel = enum(u8) {
    x_x_logarithm,
    d_x_x_logarithm,
    d_xt_x_logarithm,
    d_x_d_x_pole,
    d_xt_d_xt_pole,
};

/// FermionSpherePairKernel records the chiral derivative count of one free-fermion pair kernel.
pub const FermionSpherePairKernel = struct {
    derivative_total: u8 = 0,
};

fn validBosonProfile(profile: DerivativeProfile) bool {
    if (profile.holomorphic != 0 and profile.antiholomorphic != 0) return false;
    return profile.holomorphic <= 1 and profile.antiholomorphic <= 1;
}

/// classifyFreeBosonSphereKernel returns the primitive free-boson sphere kernel for one field pair.
pub fn classifyFreeBosonSphereKernel(left: DerivativeProfile, right: DerivativeProfile) ?BosonSpherePairKernel {
    if (!validBosonProfile(left) or !validBosonProfile(right)) return null;

    const holomorphic_total = left.holomorphic + right.holomorphic;
    const antiholomorphic_total = left.antiholomorphic + right.antiholomorphic;

    if (holomorphic_total == 0 and antiholomorphic_total == 0) return .x_x_logarithm;
    if (holomorphic_total == 1 and antiholomorphic_total == 0) return .d_x_x_logarithm;
    if (holomorphic_total == 0 and antiholomorphic_total == 1) return .d_xt_x_logarithm;
    if (holomorphic_total == 2 and antiholomorphic_total == 0) return .d_x_d_x_pole;
    if (holomorphic_total == 0 and antiholomorphic_total == 2) return .d_xt_d_xt_pole;
    return null;
}

fn validFermionProfile(comptime antiholomorphic: bool, profile: DerivativeProfile) bool {
    if (antiholomorphic) {
        if (profile.holomorphic != 0) return false;
        return true;
    }
    if (profile.antiholomorphic != 0) return false;
    return true;
}

/// classifyFreeFermionSphereKernel returns the primitive free-fermion sphere kernel for one chirality.
pub fn classifyFreeFermionSphereKernel(comptime antiholomorphic: bool, left: DerivativeProfile, right: DerivativeProfile) ?FermionSpherePairKernel {
    if (!validFermionProfile(antiholomorphic, left) or !validFermionProfile(antiholomorphic, right)) return null;

    return .{ .derivative_total = if (antiholomorphic)
        left.antiholomorphic + right.antiholomorphic
    else
        left.holomorphic + right.holomorphic };
}

test "primitive boson kernels match the free-boson sphere rule inventory" {
    const testing = @import("std").testing;

    try testing.expectEqual(BosonSpherePairKernel.x_x_logarithm, classifyFreeBosonSphereKernel(.{}, .{}).?);
    try testing.expectEqual(BosonSpherePairKernel.d_x_x_logarithm, classifyFreeBosonSphereKernel(.{ .holomorphic = 1 }, .{}).?);
    try testing.expectEqual(BosonSpherePairKernel.d_x_x_logarithm, classifyFreeBosonSphereKernel(.{}, .{ .holomorphic = 1 }).?);
    try testing.expectEqual(BosonSpherePairKernel.d_xt_x_logarithm, classifyFreeBosonSphereKernel(.{ .antiholomorphic = 1 }, .{}).?);
    try testing.expectEqual(BosonSpherePairKernel.d_x_d_x_pole, classifyFreeBosonSphereKernel(.{ .holomorphic = 1 }, .{ .holomorphic = 1 }).?);
    try testing.expectEqual(BosonSpherePairKernel.d_xt_d_xt_pole, classifyFreeBosonSphereKernel(.{ .antiholomorphic = 1 }, .{ .antiholomorphic = 1 }).?);
    try testing.expectEqual(@as(?BosonSpherePairKernel, null), classifyFreeBosonSphereKernel(.{ .holomorphic = 1 }, .{ .antiholomorphic = 1 }));
}

test "primitive fermion kernels keep the two chiral copies separate" {
    const testing = @import("std").testing;

    try testing.expectEqual(FermionSpherePairKernel{ .derivative_total = 0 }, classifyFreeFermionSphereKernel(false, .{}, .{}).?);
    try testing.expectEqual(FermionSpherePairKernel{ .derivative_total = 1 }, classifyFreeFermionSphereKernel(false, .{ .holomorphic = 1 }, .{}).?);
    try testing.expectEqual(FermionSpherePairKernel{ .derivative_total = 2 }, classifyFreeFermionSphereKernel(false, .{ .holomorphic = 1 }, .{ .holomorphic = 1 }).?);
    try testing.expectEqual(FermionSpherePairKernel{ .derivative_total = 0 }, classifyFreeFermionSphereKernel(true, .{}, .{}).?);
    try testing.expectEqual(FermionSpherePairKernel{ .derivative_total = 1 }, classifyFreeFermionSphereKernel(true, .{ .antiholomorphic = 1 }, .{}).?);
    try testing.expectEqual(FermionSpherePairKernel{ .derivative_total = 7 }, classifyFreeFermionSphereKernel(true, .{ .antiholomorphic = 3 }, .{ .antiholomorphic = 4 }).?);
    try testing.expectEqual(@as(?FermionSpherePairKernel, null), classifyFreeFermionSphereKernel(false, .{ .antiholomorphic = 1 }, .{}));
}
