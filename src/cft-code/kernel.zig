const operators = @import("expressions/operators.zig");
const theory = @import("theory/theory.zig");
const tensor = @import("tensor-code");

/// Stream groups coefficient and projected-local-term records emitted by kernels.
pub const Stream = struct {
    /// Scalar is the numeric coefficient type used by the kernel skeleton.
    pub const Scalar = f64;
    /// CoordinateFactor names a coordinate factor in a coefficient store.
    pub const CoordinateFactor = u32;

    /// CoeffTerm is one streamed scalar-coordinate-tensor coefficient term.
    pub const CoeffTerm = struct {
        scalar: Scalar,
        coordinate_factor: CoordinateFactor,
        tensor_structure: ?tensor.TensorExprId,
    };

    /// LocalTerm is one streamed projected local OPE term.
    pub const LocalTerm = struct {
        coeff: CoeffTerm,
        insertion: operators.OperatorInsertion,
        body: operators.OperatorBodyId,
    };
};

/// Call groups compact input records passed to generated kernels.
pub const Call = struct {
    /// RationalLabel stores one exact rational operator label.
    pub const RationalLabel = struct {
        numerator: i64,
        denominator: i64,
    };

    /// LabelValue stores one compact runtime operator label.
    pub const LabelValue = union(enum) {
        integer: i64,
        rational: RationalLabel,
        tensor: tensor.TensorExprId,
        symbol: u32,
    };

    /// LabelStore is the immutable label arena carried by a MultiOp.
    pub const LabelStore = struct {
        values: []const LabelValue,
    };

    /// LocalOp is one runtime local operator with labels stored out-of-line.
    pub const LocalOp = struct {
        insertion: operators.OperatorInsertion,
        kind: operators.OperatorKindId,
        labels: theory.Id.LabelSpan,
        /// Equal nonzero ids mark factors in the same normal-ordered product.
        normal_order_group: u16 = 0,
    };

    /// MultiOp is an ordered collection of local operators and their label store.
    pub const MultiOp = struct {
        operators: []const LocalOp,
        labels: *const LabelStore,
    };

    /// OpeProjection stores the target and filters for projected OPE output.
    pub const OpeProjection = struct {
        target: OpeTarget,
        target_weights: ?theory.Runtime.ConformalWeights,
        quantum_filters: []const theory.Label.QuantumFilter,
        max_level: ?theory.Runtime.LevelBound,
    };

    /// OpeTarget tells the OPE where the projected local term is inserted.
    pub const OpeTarget = union(enum) {
        first_insertion,
        explicit: operators.OperatorInsertion,
    };

    /// BasisQuery stores filters for streamed operator or state generation.
    pub const BasisQuery = struct {
        weights: ?theory.Runtime.ConformalWeights,
        quantum_filters: []const theory.Label.QuantumFilter,
        domain: ?theory.Runtime.OperatorDomain,
        support: ?theory.Runtime.ChiralSupport,
        max_level: ?theory.Runtime.LevelBound,
        finite_projections: []const theory.Id.FiniteProjection,
        descendants: DescendantFilter,
    };

    /// DescendantFilter limits which mode descendants basis generation may use.
    pub const DescendantFilter = struct {
        mode_algebras: []const theory.Id.ModeAlgebra,
        max_level: ?theory.Runtime.LevelBound,
    };

    /// BasisState is one streamed candidate body with computed weights.
    pub const BasisState = struct {
        body: operators.OperatorBodyId,
        weights: theory.Runtime.ConformalWeights,
    };
};

const Body = struct {
    const Schema = struct {
        bulk_kinds: []const operators.OperatorKind,
        boundary_kind_ids: []const operators.OperatorKindId = &.{},
        boundary_changing_kinds: []const theory.Boundary.ChangingKind = &.{},
    };

    const CanonicalResult = struct {
        coeff: Stream.Scalar,
        body: ?operators.OperatorBodyId,
    };

    fn Store(comptime schema: Schema) type {
        return struct {
            const operator_schema = schema;

            /// atomic constructs an atomic operator body handle.
            pub fn atomic(kind: operators.OperatorKindId, labels: theory.Id.LabelSpan) !operators.OperatorBodyId {
                _ = labels;
                return @as(operators.OperatorBodyId, kind);
            }

            /// normalOrdered constructs a canonical normal-product body handle.
            pub fn normalOrdered(factors: []const operators.OperatorBodyId) !CanonicalResult {
                if (factors.len == 0) {
                    return .{ .coeff = 1, .body = null };
                }
                return .{ .coeff = 1, .body = factors[0] };
            }
        };
    }
};

/// CFTKernel returns the generated kernel type for a bulk CFT preset.
pub fn CFTKernel(comptime spec: theory.Spec.CFT) type {
    return struct {
        const cft_spec = spec;
        const bulk_operator_kinds = spec.bulk_operator_kinds;

        /// Bodies constructs operator bodies using this preset's schema.
        pub const Bodies = Body.Store(.{
            .bulk_kinds = spec.bulk_operator_kinds,
        });

        /// ope computes the projected OPE of any number of local operators.
        pub fn ope(input: Call.MultiOp, projection: Call.OpeProjection, sink: anytype) !void {
            _ = input;
            _ = projection;
            _ = sink;
            return error.NotImplemented;
        }

        /// correlator evaluates any number of local operators with a config.
        pub fn correlator(config: *const theory.Runtime.CorrelatorConfig, input: Call.MultiOp, sink: anytype) !void {
            _ = config;
            _ = input;
            _ = sink;
            return error.NotImplemented;
        }

        /// basis streams operator or state candidates satisfying a query.
        pub fn basis(query: Call.BasisQuery, sink: anytype) !void {
            _ = query;
            _ = sink;
            return error.NotImplemented;
        }
    };
}

/// BCFTKernel returns the generated kernel type for a BCFT extension.
pub fn BCFTKernel(comptime Bulk: type, comptime bcft: theory.Spec.BCFT) type {
    return struct {
        const bulk = Bulk;
        const bcft_spec = bcft;

        /// Bodies constructs bulk, boundary, and boundary-changing bodies.
        pub const Bodies = Body.Store(.{
            .bulk_kinds = Bulk.bulk_operator_kinds,
            .boundary_kind_ids = bcft.boundary_operator_kinds,
            .boundary_changing_kinds = bcft.boundary_changing_kinds,
        });

        /// ope computes the projected OPE for this BCFT extension.
        pub fn ope(input: Call.MultiOp, projection: Call.OpeProjection, sink: anytype) !void {
            _ = input;
            _ = projection;
            _ = sink;
            return error.NotImplemented;
        }

        /// correlator evaluates bulk and boundary local operators with a config.
        pub fn correlator(config: *const theory.Runtime.CorrelatorConfig, input: Call.MultiOp, sink: anytype) !void {
            _ = config;
            _ = input;
            _ = sink;
            return error.NotImplemented;
        }

        /// basis streams bulk, boundary, or boundary-changing candidates.
        pub fn basis(query: Call.BasisQuery, sink: anytype) !void {
            _ = query;
            _ = sink;
            return error.NotImplemented;
        }
    };
}

test "MultiOp carries local operators and labels" {
    const testing = @import("std").testing;

    const labels = Call.LabelStore{
        .values = &.{ .{ .integer = 7 } },
    };
    const ops = [_]Call.LocalOp{
        .{
            .insertion = .{ .single = .{ .position = 1, .derivatives = 0 } },
            .kind = 2,
            .labels = 0,
        },
    };
    const input = Call.MultiOp{
        .operators = &ops,
        .labels = &labels,
    };

    try testing.expectEqual(@as(usize, 1), input.operators.len);
    try testing.expectEqual(@as(operators.OperatorKindId, 2), input.operators[0].kind);
    switch (input.labels.values[0]) {
        .integer => |value| try testing.expectEqual(@as(i64, 7), value),
        else => return error.UnexpectedLabelKind,
    }
}

test "BCFT kernel extends bulk schema without mutating bulk schema" {
    const testing = @import("std").testing;

    const bulk_spec = theory.Spec.CFT{
        .sectors = &.{},
        .bulk_operator_kinds = &.{},
        .conformal_structure = 0,
        .conformal_structures = &.{},
        .quantum_names = &.{},
        .label_schemas = &.{},
        .conventions = &.{},
        .weight_rules = &.{},
        .quantum_rules = &.{},
        .statistics_rules = &.{},
        .strategy_support_rules = &.{},
        .wick_rule_sets = &.{},
        .pairing_data = &.{},
        .zero_mode_rule_sets = &.{},
        .correlator_configs = &.{},
        .local_ope_configs = &.{},
        .cocycle_tables = &.{},
        .presentations = &.{},
        .finite_projections = &.{},
        .lattices = &.{},
        .mode_algebras = &.{},
        .mode_action_rules = &.{},
    };

    const bcft_spec = theory.Spec.BCFT{
        .name = "empty boundary extension",
        .bulk = 0,
        .boundary_conditions = &.{},
        .boundary_stacks = &.{},
        .boundary_stress_tensor = .{ .kind = 0, .labels = 0 },
        .boundary_spin = &.{},
        .boundary_operator_kinds = &.{ 1, 2 },
        .boundary_changing_kinds = &.{},
        .wick_rule_sets = &.{},
        .pairing_data = &.{},
        .zero_mode_rule_sets = &.{},
        .correlator_configs = &.{},
        .local_ope_configs = &.{},
    };

    const Bulk = CFTKernel(bulk_spec);
    const BoundaryKernel = BCFTKernel(Bulk, bcft_spec);

    try testing.expectEqual(@as(usize, 0), Bulk.Bodies.operator_schema.boundary_kind_ids.len);
    try testing.expectEqual(@as(usize, 2), BoundaryKernel.Bodies.operator_schema.boundary_kind_ids.len);
    try testing.expectEqual(@as(operators.OperatorKindId, 1), BoundaryKernel.Bodies.operator_schema.boundary_kind_ids[0]);
}
