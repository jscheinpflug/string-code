const std = @import("std");

/// EpsilonSign fixes whether the regulated worldsheet dimension is 2-epsilon or 2+epsilon.
pub const EpsilonSign = enum(u8) { minus, plus };

/// SubtractionScheme selects the pole-subtraction convention.
pub const SubtractionScheme = enum(u8) {
    minimal,
    modified_minimal,
};

/// BFieldEpsilonScheme records the antisymmetric-tensor epsilon-frame policy.
pub const BFieldEpsilonScheme = union(enum(u8)) {
    none,
    frame_epsilon: u32,
};

/// DimRegMS describes one dimensional-regularization/minimal-subtraction job scheme.
pub const DimRegMS = struct {
    epsilon_symbol: u32 = 0,
    mu_symbol: u32 = 0,
    dimension_base: u8 = 2,
    epsilon_sign: EpsilonSign = .minus,
    subtraction: SubtractionScheme = .minimal,
    b_field_epsilon: BFieldEpsilonScheme = .none,

    /// isStringbookCompatible reports whether the scheme matches the fixed R4 plan defaults.
    pub fn isStringbookCompatible(self: DimRegMS) bool {
        return self.dimension_base == 2 and self.epsilon_sign == .minus and self.subtraction == .minimal;
    }
};

/// stringbookMS returns the fixed dimensional-regularization/minimal-subtraction scheme.
pub fn stringbookMS() DimRegMS {
    return .{};
}

test "stringbook scheme is fixed to 2-minus-epsilon minimal subtraction" {
    const testing = std.testing;
    const scheme = stringbookMS();
    try testing.expect(scheme.isStringbookCompatible());
    try testing.expect(scheme.b_field_epsilon == .none);
}
