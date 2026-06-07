const tensor = @import("tensor-code");

/// Rational stores one normalized exact rational number.
pub const Rational = struct {
    numerator: i64,
    denominator: i64,
};

fn absInt(value: i64) u64 {
    if (value == @import("std").math.minInt(i64)) return @as(u64, 1) << 63;
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

/// rational constructs a normalized exact rational number.
pub fn rational(numerator: i64, denominator: i64) ?Rational {
    if (denominator == 0) return null;
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

/// integer constructs an exact rational integer.
pub fn integer(value: i64) Rational {
    return .{ .numerator = value, .denominator = 1 };
}

/// CoordinateDifference stores one ordered coordinate difference.
pub const CoordinateDifference = struct {
    left: Variable,
    right: Variable,
};

/// CoordinateKernel stores one coordinate-dependent kernel factor.
pub const CoordinateKernel = union(enum) {
    difference_power: struct { coordinate: CoordinateDifference, exponent: i16 },
    logarithm: CoordinateDifference,
    green_kernel: struct { name: []const u8, coordinate: CoordinateDifference, left_derivatives: u8 = 0, right_derivatives: u8 = 0 },
    green_exponential: CoordinateDifference,
};

/// CoordinateFactor stores a coordinate kernel with its rational derivative multiplier.
pub const CoordinateFactor = struct {
    scalar: Rational = .{ .numerator = 1, .denominator = 1 },
    kernel: CoordinateKernel,
};

/// A coefficient is a sum of rational functions multiplied by a tensor structure
pub const Coeff = struct {
    summands: []const CoeffSummand,
};

const CoeffSummand = struct {
    rational_function: RationalFunction,
    tensor_structure: tensor.TensorStructure,
};

const RationalFunction = struct {
    factors: []const Factor,
};

const Factor = struct {
    base: Polynomial,
    exponent: i16,
};

const Polynomial = struct {
    terms: []const PolynomialTerm,
};

const PolynomialTerm = struct {
    monomial_coefficient: Scalar,
    monomial: Monomial,
};

const Scalar = f32;

const Monomial = struct {
    terms: []const MonomialTerm,
};

const MonomialTerm = struct {
   variable: Variable,
   power: u16,
};

/// Variables are internally assigned numeric identifiers
pub const Variable = u32;
