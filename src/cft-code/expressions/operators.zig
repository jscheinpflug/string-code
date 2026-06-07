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

/// Operator insertion data are specified by a position and a number of derivatives
pub const OperatorInsertion = union(enum) {
    single: struct {
        position: coefficient.Variable,
        derivatives: u8,
        },
    pair: struct {
        holomorphic_position: coefficient.Variable,
        antiholomorphic_position: coefficient.Variable,
        holomorphic_derivatives: u8,
        antiholomorphic_derivatives: u8,
    },
};
