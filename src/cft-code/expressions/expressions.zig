const coefficient = @import("coefficient.zig");
const operators = @import("operators.zig");

/// A symbolic expression encountered in worldsheet calculations
pub const Expr = struct {
    summands: []const ExprSummand
};
/// Each summand is a local operator with a coefficient
pub const ExprSummand = struct {
    coeff: coefficient.Coeff,
    operators: operators.Operator
};
