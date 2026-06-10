const coefficient = @import("coefficient.zig");
const tensor = @import("tensor-code");

/// A local operator inserted at a point
pub const Operator = struct {
    insertion: OperatorInsertion,
    body: OperatorBodyId,
};

/// An identifier for operator body
pub const OperatorBodyId = u32;

/// An operator body is either atomic or normal-ordered
pub const OperatorBody = union(enum) {
    identity,
    atomic: AtomicBody,
    normal_ordered: []const OperatorBodyId,
};

/// An atomic operator body comes in different kinds and can carry extra information
pub const AtomicBody = struct {
    kind: OperatorKindId,
    extra: OperatorExtraId,
};

/// An identifier for operator kind
pub const OperatorKindId = u32;
/// An identifier for operator extra information
pub const OperatorExtraId = u32;

/// Defines the various kinds of operators
pub const OperatorKind = struct {
    holomorphicity: Holomorphicity,
    conformal_weights: ConformalWeights,
    quantum_numbers: tensor.QuantumNumbers,
    supported_correlator_tactics: []const CorrelatorTactic,
};

/// Determines whether an operator is holomorphic/antiholomorphic or both
pub const Holomorphicity = enum {
    holomorphic,
    antiholomorphic,
    both,
};

/// ConformalWeights stores fixed weights or a rule for computing them.
pub const ConformalWeights = union(enum) {
    fixed: FixedConformalWeights,
    computed: WeightRuleId,
};

/// FixedConformalWeights stores optional left and right conformal weights.
pub const FixedConformalWeights = struct {
    h: ?f16,
    hbar: ?f16,
};

/// WeightRuleId names a rule that computes conformal weights from labels.
pub const WeightRuleId = u16;

/// A tactic for the the evaluation of correlators
pub const CorrelatorTactic = enum {
    abstract,
    wick,
    bosonize,
};

/// Point is either a finite coordinate variable or the local chart at infinity.
pub const Point = struct {
    raw: coefficient.Variable,

    /// infinity_variable is the compact sentinel used only after an infinity call is detected.
    pub const infinity_variable: coefficient.Variable = @import("std").math.maxInt(coefficient.Variable);

    /// finite constructs a finite insertion point from a coordinate variable.
    pub fn finite(raw_variable: coefficient.Variable) Point {
        return .{ .raw = raw_variable };
    }

    /// infinity constructs the insertion point at infinity.
    pub fn infinity() Point {
        return .{ .raw = infinity_variable };
    }

    /// isInfinity reports whether this point is the infinity chart.
    pub fn isInfinity(self: Point) bool {
        return self.raw == infinity_variable;
    }

    /// variable returns the finite variable, or null for infinity.
    pub fn variable(self: Point) ?coefficient.Variable {
        return if (self.isInfinity()) null else self.raw;
    }
};

/// Operator insertion data are specified by a point and a number of derivatives.
pub const OperatorInsertion = union(enum) {
    single: struct {
        position: Point,
        derivatives: u8,
    },
    pair: struct {
        holomorphic_position: Point,
        antiholomorphic_position: Point,
        holomorphic_derivatives: u8,
        antiholomorphic_derivatives: u8,
    },
};
