const std = @import("std");
const shared = @import("shared.zig");
const declare = shared.declare;

const operators = @import("../expressions/operators.zig");
const Handle = shared.Handle;
const Local = shared.Local;
const Builder = *shared.Local;
const Operator = *shared.LocalOperator;
const Spec = declare.Spec;
const wick = declare.wick;
const zero_mode = declare.zero_mode;

const namespace = "free_boson";
const scalars = declare.scalars;
const RuleScalar = @TypeOf(scalars.one());
const alpha_prime_atom = scalars.atom(namespace, "alpha_prime");
const k_disk_atom = scalars.atom(namespace, "K_D2");
const neumann_projector_ref = declare.configRef(namespace, "neumann_projector");
const dirichlet_projector_ref = declare.configRef(namespace, "dirichlet_projector");
const bulk_boundary_projector_ref = declare.configRef(namespace, "bulk_boundary_projector");
const dirichlet_position_ref = declare.configRef(namespace, "dirichlet_position");
const chan_paton_ref = declare.configRef(namespace, "chan_paton");
const target_dimension_ref = declare.configRef(namespace, "target_dimension");

const Family = enum {
    x,
    d_x,
    d_xt,
    exp_x,
    profile_x,
    d_x_boundary,
    exp_x_boundary,
    profile_x_boundary,
};

const ZeroSector = enum {
    bulk,
    boundary,
    torus,
};

fn kind(comptime family: Family) operators.OperatorKindId {
    return declare.familyKind(namespace, family);
}

fn zeroSector(comptime sector: ZeroSector) zero_mode.Sector {
    return declare.sectorId(namespace, sector);
}

fn rawToken(value: anytype) u32 {
    return @intFromEnum(value);
}

fn token(comptime T: type, id: u32) T {
    return @enumFromInt(if (id == 0) 1 else id);
}

fn stableNameId(comptime name: []const u8) u32 {
    var hash: u32 = 2166136261;
    inline for (name) |byte| {
        hash = (hash ^ @as(u32, byte)) *% 16777619;
    }
    return if (hash == 0) 1 else hash;
}

fn stableSubspaceId(comptime dimensions: []const u16) u32 {
    var hash: u32 = 2166136261;
    inline for (dimensions) |dimension| {
        hash = (hash ^ @as(u32, dimension & 0xff)) *% 16777619;
        hash = (hash ^ @as(u32, dimension >> 8)) *% 16777619;
    }
    return if (hash == 0) 1 else hash;
}

fn projectorId(comptime rank: u8, hash: u32) u32 {
    return (@as(u32, rank) << 24) | (hash & 0x00ff_ffff);
}

fn polynomialProfileTerm(term: anytype) struct { coefficient: Handle.ProfileCoefficient, power: u16 } {
    const Term = @TypeOf(term);
    const info = @typeInfo(Term);
    if (info != .@"struct" or !info.@"struct".is_tuple or info.@"struct".fields.len != 2) {
        @compileError("polynomial profile terms must be .{ coefficient, power } tuples");
    }
    return .{ .coefficient = term[0], .power = term[1] };
}

fn polynomialProfileId(point: Handle.TargetPoint, terms: anytype) u32 {
    var hash = rawToken(point) ^ 0x9e37_79b9;
    inline for (terms) |raw_term| {
        const term = polynomialProfileTerm(raw_term);
        hash = (hash ^ rawToken(term.coefficient)) *% 16777619;
        hash = (hash ^ @as(u32, term.power)) *% 16777619;
    }
    return if (hash == 0) 1 else hash;
}

const TargetSpace = struct {
    /// subspace names a target-space projector onto a coordinate subspace.
    pub fn subspace(comptime dimensions: []const u16) Handle.TensorProjector {
        return token(Handle.TensorProjector, projectorId(@intCast(dimensions.len), stableSubspaceId(dimensions)));
    }

    /// complement names the complementary target-space projector.
    pub fn complement(comptime dimensions: []const u16) Handle.TensorProjector {
        return token(Handle.TensorProjector, projectorId(0, stableSubspaceId(dimensions) ^ 0xa5a5_a5a5));
    }

    /// point names a target-space point used by boundary conditions.
    pub fn point(comptime name: []const u8) Handle.TargetPoint {
        return token(Handle.TargetPoint, stableNameId(name));
    }

    /// boundaryStack names Chan-Paton data for a stacked boundary condition.
    pub fn boundaryStack(comptime name: []const u8) Handle.BoundaryStack {
        return token(Handle.BoundaryStack, stableNameId(name));
    }
};

const FreeBosonConfig = struct {
    dimension: u16,
};

/// freeBoson builds the generated preset type for a noncompact free-boson CFT.
pub fn freeBoson(comptime cfg: FreeBosonConfig) type {
    return struct {
        /// op exposes free-boson local operator builders.
        pub const op = FreeBosonOp;
        /// profile exposes profile-presentation builders.
        pub const profile = ProfileOp;
        /// target exposes deterministic target-space tokens for preset data.
        pub const target = TargetSpace;
        /// config exposes named correlator configs for this preset.
        pub const config = FreeBosonCorrelatorConfig(cfg);
        /// text exposes bounded result-inspection sinks.
        pub const text = shared.text;
        /// local constructs a label-preserving local-operator builder.
        pub fn local(allocator: std.mem.Allocator) !Builder {
            return shared.Local.init(allocator);
        }

        /// correlator streams rule matches for free-boson insertions.
        pub fn correlator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
            return shared.streamCorrelator(config_ptr, ops, sink);
        }
    };
}

const FreeBosonOp = struct {
    /// X builds an explicit bulk free-boson field insertion.
    pub fn X(local: anytype, mu: Handle.Index, z: Handle.Coord, zbar: Handle.Coord) !Operator {
        return declare.operatorBuilder(sphereOperator(.x)).pair(local, z, zbar, .{mu});
    }

    /// dX builds a holomorphic derivative field insertion.
    pub fn dX(local: anytype, mu: Handle.Index, n: u8, z: Handle.Coord) !Operator {
        return declare.operatorBuilder(sphereOperator(.d_x)).single(local, z, n, .{mu});
    }

    /// dXt builds an antiholomorphic derivative field insertion.
    pub fn dXt(local: anytype, mu: Handle.Index, n: u8, zbar: Handle.Coord) !Operator {
        return declare.operatorBuilder(sphereOperator(.d_xt)).single(local, zbar, n, .{mu});
    }

    /// expX builds a normal-ordered plane-wave insertion.
    pub fn expX(local: anytype, k: Handle.Momentum, z: Handle.Coord, zbar: Handle.Coord) !Operator {
        return declare.operatorBuilder(sphereOperator(.exp_x)).pair(local, z, zbar, .{k});
    }

    /// profile builds a target-space profile insertion.
    pub fn profile(local: anytype, f: Handle.Profile, z: Handle.Coord, zbar: Handle.Coord) !Operator {
        return declare.operatorBuilder(sphereOperator(.profile_x)).pair(local, z, zbar, .{f});
    }

    /// profileVector builds a vector-valued target-space profile insertion.
    pub fn profileVector(local: anytype, f: Handle.Profile, nu: Handle.Index, z: Handle.Coord, zbar: Handle.Coord) !Operator {
        return declare.operatorBuilder(profile_vector_operator).pair(local, z, zbar, .{ f, nu });
    }
};

const ProfileOp = struct {
    /// positionSpace selects the exact residual position-space profile presentation.
    pub fn positionSpace(f: Handle.TargetFunction) Handle.Profile {
        return shared.profileHandle(.position_space, rawToken(f));
    }

    /// fourier selects the Fourier-space profile presentation.
    pub fn fourier(f_hat: Handle.FourierTransform) Handle.Profile {
        return shared.profileHandle(.fourier, rawToken(f_hat));
    }

    /// polynomialRnc selects a finite polynomial profile presentation.
    pub fn polynomialRnc(point: Handle.TargetPoint, terms: anytype) Handle.Profile {
        return shared.profileHandle(.polynomial_rnc, polynomialProfileId(point, terms));
    }
};

fn holomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .position), wick.coord(.right, .position));
}

fn antiholomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .position), wick.coord(.right, .position));
}

fn bulkHolomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .holomorphic), wick.coord(.right, .holomorphic));
}

fn bulkAntiholomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .antiholomorphic), wick.coord(.right, .antiholomorphic));
}

fn bulkToBoundaryHolomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .holomorphic), wick.coord(.right, .position));
}

fn bulkToBoundaryAntiholomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .antiholomorphic), wick.coord(.right, .position));
}

fn singleToBulkHolomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .position), wick.coord(.right, .holomorphic));
}

fn singleToBulkAntiholomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .position), wick.coord(.right, .antiholomorphic));
}

fn freeBosonDxDx(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(scalars.neg(alpha), 2), .{ .metric = .{
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, holomorphicDifference(), -2, .{ .include_left = true, .include_right = true });
}

fn freeBosonDxtDxt(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(scalars.neg(alpha), 2), .{ .metric = .{
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, antiholomorphicDifference(), -2, .{ .include_left = true, .include_right = true });
}

fn freeBosonDxExpX(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPoleWithResiduals(scalars.div(scalars.neg(scalars.i(alpha)), 2), .{ .momentum_index = .{
        .momentum = wick.label(.right, 0),
        .index = wick.label(.left, 0),
    } }, holomorphicDifference(), -1, .{ .include_left = true }, &.{.right});
}

fn freeBosonDxProfile(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedActionPoleWithResiduals(scalars.div(scalars.neg(alpha), 2), .none, holomorphicDifference(), -1, .{ .include_left = true }, &.{
        wick.profileDerivative(wick.label(.right, 0), wick.label(.left, 0)),
    }, &.{.right});
}

fn freeBosonDxtExpX(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPoleWithResiduals(scalars.div(scalars.neg(scalars.i(alpha)), 2), .{ .momentum_index = .{
        .momentum = wick.label(.right, 0),
        .index = wick.label(.left, 0),
    } }, antiholomorphicDifference(), -1, .{ .include_left = true }, &.{.right});
}

fn freeBosonDxtProfile(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedActionPoleWithResiduals(scalars.div(scalars.neg(alpha), 2), .none, antiholomorphicDifference(), -1, .{ .include_left = true }, &.{
        wick.profileDerivative(wick.label(.right, 0), wick.label(.left, 0)),
    }, &.{.right});
}

fn freeBosonXX(comptime alpha: RuleScalar) wick.Expr {
    const scalar = scalars.div(scalars.neg(alpha), 2);
    return wick.expr(&.{
        wick.term(&.{wick.scalar(scalar)}, &.{wick.logarithm(bulkHolomorphicDifference())}, &.{.{ .metric = .{
            .left = wick.label(.left, 0),
            .right = wick.label(.right, 0),
        } }}),
        wick.term(&.{wick.scalar(scalar)}, &.{wick.logarithm(bulkAntiholomorphicDifference())}, &.{.{ .metric = .{
            .left = wick.label(.left, 0),
            .right = wick.label(.right, 0),
        } }}),
    });
}

fn freeBosonDxX(comptime alpha: RuleScalar) wick.Expr {
    return wick.expr(&.{wick.term(&.{wick.scalar(scalars.div(scalars.neg(alpha), 2))}, &.{
        wick.differentiatedLogarithm(singleToBulkHolomorphicDifference(), .{ .include_left = true }),
    }, &.{.{ .metric = .{
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }})});
}

fn freeBosonDxtX(comptime alpha: RuleScalar) wick.Expr {
    return wick.expr(&.{wick.term(&.{wick.scalar(scalars.div(scalars.neg(alpha), 2))}, &.{
        wick.differentiatedLogarithm(singleToBulkAntiholomorphicDifference(), .{ .include_left = true }),
    }, &.{.{ .metric = .{
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }})});
}

fn freeBosonExpXExpX(comptime alpha: RuleScalar) wick.Expr {
    return wick.expr(&.{wick.termWithResiduals(&.{wick.scalar(scalars.div(alpha, 2))}, &.{
        .{ .green_exponential = bulkHolomorphicDifference() },
        .{ .green_exponential = bulkAntiholomorphicDifference() },
    }, &.{.{ .momentum_pair = .{
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }}, &.{}, &.{ .left, .right })});
}

fn sphereZeroSpec(comptime normalization: RuleScalar) [1]Spec.ZeroModeRule {
    return [_]Spec.ZeroModeRule{
        .{ .sector = zeroSector(.bulk), .expr = .{ .free_boson_constant_mode = .{
            .exp_kind_ids = &.{kind(.exp_x)},
            .profile_kind_ids = &.{kind(.profile_x)},
            .normalization = .{
                .scalar = normalization,
                .two_pi_power = .{ .target_dimension = target_dimension_ref },
            },
        } } },
    };
}

fn sphereZeroStorage() [1]zero_mode.Rule {
    const spec = sphereZeroSpec(.one);
    return Spec.zeroModeRules(&spec);
}

const sphere_operator_spec = [_]Spec.Operator{
    .{ .name = "X", .kind = kind(.x), .support = .bulk_pair, .insertion = .pair, .labels = &.{.index}, .statistics = .bosonic },
    .{ .name = "dX", .kind = kind(.d_x), .support = .holomorphic, .insertion = .single, .labels = &.{.index}, .statistics = .bosonic },
    .{ .name = "dXt", .kind = kind(.d_xt), .support = .antiholomorphic, .insertion = .single, .labels = &.{.index}, .statistics = .bosonic },
    .{ .name = "expX", .kind = kind(.exp_x), .support = .bulk_pair, .insertion = .pair, .labels = &.{.momentum}, .statistics = .bosonic, .zero_mode_consumable = true },
    .{ .name = "profile", .kind = kind(.profile_x), .support = .bulk_pair, .insertion = .pair, .labels = &.{.profile}, .statistics = .bosonic, .zero_mode_consumable = true },
};

fn sphereWickSpec(comptime alpha: RuleScalar) [10]Spec.WickRule {
    return [_]Spec.WickRule{
        .{ .left = kind(.x), .right = kind(.x), .expr = freeBosonXX(alpha) },
        .{ .left = kind(.d_x), .right = kind(.d_x), .expr = freeBosonDxDx(alpha) },
        .{ .left = kind(.d_xt), .right = kind(.d_xt), .expr = freeBosonDxtDxt(alpha) },
        .{ .left = kind(.d_x), .right = kind(.x), .expr = freeBosonDxX(alpha) },
        .{ .left = kind(.d_xt), .right = kind(.x), .expr = freeBosonDxtX(alpha) },
        .{ .left = kind(.d_x), .right = kind(.exp_x), .expr = freeBosonDxExpX(alpha) },
        .{ .left = kind(.d_xt), .right = kind(.exp_x), .expr = freeBosonDxtExpX(alpha) },
        .{ .left = kind(.d_x), .right = kind(.profile_x), .expr = freeBosonDxProfile(alpha) },
        .{ .left = kind(.d_xt), .right = kind(.profile_x), .expr = freeBosonDxtProfile(alpha) },
        .{ .left = kind(.exp_x), .right = kind(.exp_x), .expr = freeBosonExpXExpX(alpha) },
    };
}

const sphere_wick_spec = sphereWickSpec(.one);

const torus_wick_spec = [_]Spec.WickRule{
    .{ .left = kind(.x), .right = kind(.x), .coordinate_kernels = &.{.elliptic_green} },
    .{ .left = kind(.d_x), .right = kind(.d_x), .coordinate_kernels = &.{.elliptic_green} },
    .{ .left = kind(.d_xt), .right = kind(.d_xt), .coordinate_kernels = &.{.elliptic_green} },
    .{ .left = kind(.d_x), .right = kind(.x), .coordinate_kernels = &.{.elliptic_green} },
    .{ .left = kind(.d_xt), .right = kind(.x), .coordinate_kernels = &.{.elliptic_green} },
    .{ .left = kind(.d_x), .right = kind(.exp_x), .coordinate_kernels = &.{.elliptic_green} },
    .{ .left = kind(.d_xt), .right = kind(.exp_x), .coordinate_kernels = &.{.elliptic_green} },
    .{ .left = kind(.d_x), .right = kind(.profile_x), .coordinate_kernels = &.{.elliptic_green} },
    .{ .left = kind(.d_xt), .right = kind(.profile_x), .coordinate_kernels = &.{.elliptic_green} },
    .{ .left = kind(.exp_x), .right = kind(.exp_x), .coordinate_kernels = &.{.elliptic_green_exponential} },
};

const sphere_zero_spec = sphereZeroSpec(.one);

const torus_zero_spec = [_]Spec.ZeroModeRule{
    .{
        .sector = zeroSector(.torus),
        .kind = .torus_free_boson_constant,
        .consumes = &.{ kind(.exp_x), kind(.profile_x) },
    },
};

const sphere_spec = Spec.Theory{
    .operators = &sphere_operator_spec,
    .wick_rules = &sphere_wick_spec,
    .zero_modes = &sphere_zero_spec,
};

const torus_draft_spec = Spec.Theory{
    .surface = .{
        .kind = .torus,
        .coordinate_model = .elliptic,
        .modular_parameters = &.{"tau"},
        .source = .stringbook,
    },
    .operators = &sphere_operator_spec,
    .wick_rules = &torus_wick_spec,
    .zero_modes = &torus_zero_spec,
};

const boundary_operator_spec = [_]Spec.Operator{
    .{ .name = "dXBoundary", .kind = kind(.d_x_boundary), .support = .boundary, .insertion = .single, .labels = &.{.index}, .statistics = .bosonic },
    .{ .name = "expXBoundary", .kind = kind(.exp_x_boundary), .support = .boundary, .insertion = .single, .labels = &.{.momentum}, .statistics = .bosonic, .zero_mode_consumable = true },
    .{ .name = "profileBoundary", .kind = kind(.profile_x_boundary), .support = .boundary, .insertion = .single, .labels = &.{.profile}, .statistics = .bosonic, .zero_mode_consumable = true },
};

const disk_operator_spec = sphere_operator_spec ++ boundary_operator_spec;

const profile_vector_operator = Spec.Operator{ .name = "profileVector", .kind = kind(.profile_x), .support = .bulk_pair, .insertion = .pair, .labels = &.{ .profile, .index }, .statistics = .bosonic, .zero_mode_consumable = true };
const boundary_profile_vector_operator = Spec.Operator{ .name = "profileBoundaryVector", .kind = kind(.profile_x_boundary), .support = .boundary, .insertion = .single, .labels = &.{ .profile, .index }, .statistics = .bosonic, .zero_mode_consumable = true };

fn sphereOperator(comptime family: Family) Spec.Operator {
    const kind_id = kind(family);
    inline for (sphere_operator_spec) |operator| {
        if (operator.kind == kind_id) return operator;
    }
    @compileError("missing free-boson sphere operator spec");
}

fn boundaryOperator(comptime family: Family) Spec.Operator {
    const kind_id = kind(family);
    inline for (boundary_operator_spec) |operator| {
        if (operator.kind == kind_id) return operator;
    }
    @compileError("missing free-boson boundary operator spec");
}

fn assertSphereSpec(comptime wick_count: usize, comptime zero_count: usize) void {
    if (sphere_spec.wick_rules.len != wick_count) @compileError("free-boson sphere spec Wick count does not match lowered rules");
    if (sphere_spec.zero_modes.len != zero_count) @compileError("free-boson sphere spec zero-mode count does not match lowered rules");
    if (Spec.zeroModeConsumeKindCount(sphere_spec.zero_modes[0]) != 2) @compileError("free-boson sphere spec zero-mode coverage is incomplete");
}

fn assertTorusDraftSpec() void {
    if (torus_draft_spec.surface.kind != .torus) @compileError("free-boson torus draft spec surface kind is incomplete");
    if (torus_draft_spec.surface.coordinate_model != .elliptic) @compileError("free-boson torus draft spec coordinate model is incomplete");
    if (torus_draft_spec.surface.modular_parameters.len != 1) @compileError("free-boson torus draft spec modular metadata is incomplete");
    if (torus_draft_spec.surface.source != .stringbook) @compileError("free-boson torus draft spec source convention is incomplete");
    if (torus_draft_spec.operators.len != sphere_spec.operators.len) @compileError("free-boson torus draft spec operator metadata is incomplete");
    if (torus_draft_spec.wick_rules.len != sphere_spec.wick_rules.len) @compileError("free-boson torus draft spec Wick metadata is incomplete");
    if (Spec.wickCoordinateKernelCount(torus_draft_spec.wick_rules, .elliptic_green) != 9) @compileError("free-boson torus draft spec Green-kernel metadata is incomplete");
    if (Spec.wickCoordinateKernelCount(torus_draft_spec.wick_rules, .elliptic_green_exponential) != 1) @compileError("free-boson torus draft spec exponential Green-kernel metadata is incomplete");
    if (Spec.wickCoordinateKernelCount(torus_draft_spec.wick_rules, .rational_pole) != 0) @compileError("free-boson torus draft spec still uses rational pole metadata");
    if (torus_draft_spec.zero_modes.len != 1) @compileError("free-boson torus draft spec zero-mode metadata is incomplete");
    if (Spec.zeroModeConsumeKindCount(torus_draft_spec.zero_modes[0]) != 2) @compileError("free-boson torus draft spec zero-mode coverage is incomplete");
}

fn FreeBosonRules(comptime cfg: FreeBosonConfig) type {
    _ = cfg;
    const alpha = scalars.atomScalar(alpha_prime_atom);
    return struct {
        const sphere_wick_runtime_spec = sphereWickSpec(alpha);
        const sphere_wick_storage = Spec.wickRules(&sphere_wick_runtime_spec, &sphere_operator_spec);

        const sphere_wick: []const wick.Rule = &sphere_wick_storage;
    };
}

fn FreeBosonCorrelatorConfig(comptime cfg: FreeBosonConfig) type {
    const rules = FreeBosonRules(cfg);
    return struct {
        const sphere_zero_storage = sphereZeroStorage();
        comptime {
            assertSphereSpec(rules.sphere_wick.len, sphere_zero_storage.len);
            assertTorusDraftSpec();
        }

        /// sphere selects free-boson sphere Wick and zero-mode rules.
        pub const sphere = declare.correlatorConfig(.{
            .wick_rules = rules.sphere_wick,
            .zero_modes = &sphere_zero_storage,
            .config_entries = &declare.configEntries(.{
                declare.config.targetDimension(target_dimension_ref, cfg.dimension),
            }),
        }){};
    };
}

const FreeBosonBoundaryConfig = struct {
    neumann: Handle.TensorProjector,
    dirichlet: Handle.TensorProjector,
    dirichlet_position: Handle.TargetPoint,
    chan_paton: ?Handle.BoundaryStack = null,
};

const FreeBosonBoundaryOp = struct {
    /// dXBoundary builds stringbook's holomorphic boundary limit of dX.
    pub fn dXBoundary(local: anytype, mu: Handle.Index, n: u8, y: Handle.BoundaryCoord) !Operator {
        return declare.operatorBuilder(boundaryOperator(.d_x_boundary)).boundarySingle(local, y, n, .{mu});
    }

    /// expXBoundary builds a Neumann boundary plane-wave insertion.
    pub fn expXBoundary(local: anytype, k: Handle.Momentum, y: Handle.BoundaryCoord) !Operator {
        return declare.operatorBuilder(boundaryOperator(.exp_x_boundary)).boundarySingle(local, y, 0, .{k});
    }

    /// profileBoundary builds a boundary profile insertion.
    pub fn profileBoundary(local: anytype, f: Handle.Profile, y: Handle.BoundaryCoord) !Operator {
        return declare.operatorBuilder(boundaryOperator(.profile_x_boundary)).boundarySingle(local, y, 0, .{f});
    }

    /// profileBoundaryVector builds a vector-valued boundary profile insertion.
    pub fn profileBoundaryVector(local: anytype, f: Handle.Profile, nu: Handle.Index, y: Handle.BoundaryCoord) !Operator {
        return declare.operatorBuilder(boundary_profile_vector_operator).boundarySingle(local, y, 0, .{ f, nu });
    }
};

fn FreeBosonBoundaryExtension(comptime cfg: FreeBosonBoundaryConfig) type {
    const data = FreeBosonBoundaryData(cfg);
    return declare.BoundaryExtension(.{
        .op = FreeBosonBoundaryOp,
        .wick_rules = data.disk_wick,
        .zero_modes = data.disk_zero_modes,
        .config_entries = data.config_entries,
    });
}

/// boundaryExtension declares the Neumann/Dirichlet free-boson boundary extension.
pub fn boundaryExtension(comptime cfg: FreeBosonBoundaryConfig) FreeBosonBoundaryExtension(cfg) {
    return .{};
}

fn boundaryFreeBosonDxDx(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.neg(alpha), .{ .projector_metric = .{
        .projector = .{ .config = neumann_projector_ref },
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, holomorphicDifference(), -2, .{ .include_left = true, .include_right = true });
}

fn boundaryFreeBosonDxExpX(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPoleWithResiduals(scalars.neg(scalars.i(alpha)), .{ .projector_momentum_index = .{
        .projector = .{ .config = neumann_projector_ref },
        .momentum = wick.label(.right, 0),
        .index = wick.label(.left, 0),
    } }, holomorphicDifference(), -1, .{ .include_left = true }, &.{.right});
}

fn boundaryFreeBosonDxProfile(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedActionPoleWithResiduals(scalars.neg(alpha), .none, holomorphicDifference(), -1, .{ .include_left = true }, &.{
        wick.projectedProfileDerivative(.{ .config = neumann_projector_ref }, wick.label(.right, 0), wick.label(.left, 0)),
    }, &.{.right});
}

fn boundaryFreeBosonExpXExpX(comptime alpha: RuleScalar) wick.Expr {
    return wick.greenExponentialWithResiduals(alpha, .{ .projector_momentum_pair = .{
        .projector = .{ .config = neumann_projector_ref },
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, holomorphicDifference(), &.{ .left, .right });
}

fn mixedFreeBosonDxDxBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(scalars.neg(alpha), 2), .{ .projector_metric = .{
        .projector = .{ .config = bulk_boundary_projector_ref },
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, bulkToBoundaryHolomorphicDifference(), -2, .{ .include_left = true, .include_right = true });
}

fn mixedFreeBosonDxtDxBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(scalars.neg(alpha), 2), .{ .projector_metric = .{
        .projector = .{ .config = bulk_boundary_projector_ref },
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, bulkToBoundaryAntiholomorphicDifference(), -2, .{ .include_left = true, .include_right = true });
}

fn mixedFreeBosonDxExpXBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPoleWithResiduals(scalars.div(scalars.neg(scalars.i(alpha)), 2), .{ .projector_momentum_index = .{
        .projector = .{ .config = bulk_boundary_projector_ref },
        .momentum = wick.label(.right, 0),
        .index = wick.label(.left, 0),
    } }, bulkToBoundaryHolomorphicDifference(), -1, .{ .include_left = true }, &.{.right});
}

fn mixedFreeBosonDxProfileBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedActionPoleWithResiduals(scalars.div(scalars.neg(alpha), 2), .none, bulkToBoundaryHolomorphicDifference(), -1, .{ .include_left = true }, &.{
        wick.projectedProfileDerivative(.{ .config = bulk_boundary_projector_ref }, wick.label(.right, 0), wick.label(.left, 0)),
    }, &.{.right});
}

fn mixedFreeBosonDxtExpXBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPoleWithResiduals(scalars.div(scalars.neg(scalars.i(alpha)), 2), .{ .projector_momentum_index = .{
        .projector = .{ .config = bulk_boundary_projector_ref },
        .momentum = wick.label(.right, 0),
        .index = wick.label(.left, 0),
    } }, bulkToBoundaryAntiholomorphicDifference(), -1, .{ .include_left = true }, &.{.right});
}

fn mixedFreeBosonDxtProfileBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedActionPoleWithResiduals(scalars.div(scalars.neg(alpha), 2), .none, bulkToBoundaryAntiholomorphicDifference(), -1, .{ .include_left = true }, &.{
        wick.projectedProfileDerivative(.{ .config = bulk_boundary_projector_ref }, wick.label(.right, 0), wick.label(.left, 0)),
    }, &.{.right});
}

fn mixedFreeBosonExpXExpXBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.greenExponentialWithResiduals(scalars.div(alpha, 2), .{ .projector_momentum_pair = .{
        .projector = .{ .config = bulk_boundary_projector_ref },
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, bulkToBoundaryHolomorphicDifference(), &.{ .left, .right });
}

fn diskWickSpec(comptime alpha: RuleScalar) [11]Spec.WickRule {
    return [_]Spec.WickRule{
        .{ .left = kind(.d_x_boundary), .right = kind(.d_x_boundary), .expr = boundaryFreeBosonDxDx(alpha) },
        .{ .left = kind(.d_x_boundary), .right = kind(.exp_x_boundary), .expr = boundaryFreeBosonDxExpX(alpha) },
        .{ .left = kind(.d_x_boundary), .right = kind(.profile_x_boundary), .expr = boundaryFreeBosonDxProfile(alpha) },
        .{ .left = kind(.exp_x_boundary), .right = kind(.exp_x_boundary), .expr = boundaryFreeBosonExpXExpX(alpha) },
        .{ .left = kind(.d_x), .right = kind(.d_x_boundary), .expr = mixedFreeBosonDxDxBoundary(alpha) },
        .{ .left = kind(.d_xt), .right = kind(.d_x_boundary), .expr = mixedFreeBosonDxtDxBoundary(alpha) },
        .{ .left = kind(.d_x), .right = kind(.exp_x_boundary), .expr = mixedFreeBosonDxExpXBoundary(alpha) },
        .{ .left = kind(.d_xt), .right = kind(.exp_x_boundary), .expr = mixedFreeBosonDxtExpXBoundary(alpha) },
        .{ .left = kind(.d_x), .right = kind(.profile_x_boundary), .expr = mixedFreeBosonDxProfileBoundary(alpha) },
        .{ .left = kind(.d_xt), .right = kind(.profile_x_boundary), .expr = mixedFreeBosonDxtProfileBoundary(alpha) },
        .{ .left = kind(.exp_x), .right = kind(.exp_x_boundary), .expr = mixedFreeBosonExpXExpXBoundary(alpha) },
    };
}

fn diskZeroSpec(comptime normalization: RuleScalar) [1]Spec.ZeroModeRule {
    return [_]Spec.ZeroModeRule{
        .{ .sector = zeroSector(.boundary), .expr = .{ .free_boson_constant_mode = .{
            .integration_projector = neumann_projector_ref,
            .fixed_projector = dirichlet_projector_ref,
            .fixed_position = dirichlet_position_ref,
            .exp_kind_ids = &.{ kind(.exp_x), kind(.exp_x_boundary) },
            .profile_kind_ids = &.{ kind(.profile_x), kind(.profile_x_boundary) },
            .normalization = .{
                .scalar = normalization,
                .two_pi_power = .{ .projector_rank = neumann_projector_ref },
            },
        } } },
    };
}

fn diskZeroStorage() [1]zero_mode.Rule {
    const spec = diskZeroSpec(scalars.atomScalar(k_disk_atom));
    return Spec.zeroModeRules(&spec);
}

fn FreeBosonBoundaryData(comptime cfg: FreeBosonBoundaryConfig) type {
    const alpha = scalars.atomScalar(alpha_prime_atom);
    return struct {
        const disk_wick_runtime_spec = diskWickSpec(alpha);
        const disk_wick_storage = Spec.wickRules(&disk_wick_runtime_spec, &disk_operator_spec);
        const disk_zero_storage = diskZeroStorage();
        const config_storage = if (cfg.chan_paton) |stack| declare.configEntries(.{
            declare.config.tensorProjector(neumann_projector_ref, cfg.neumann),
            declare.config.tensorProjector(dirichlet_projector_ref, cfg.dirichlet),
            declare.config.tensorProjector(bulk_boundary_projector_ref, cfg.neumann),
            declare.config.targetPoint(dirichlet_position_ref, cfg.dirichlet_position),
            declare.config.boundaryStack(chan_paton_ref, stack),
        }) else declare.configEntries(.{
            declare.config.tensorProjector(neumann_projector_ref, cfg.neumann),
            declare.config.tensorProjector(dirichlet_projector_ref, cfg.dirichlet),
            declare.config.tensorProjector(bulk_boundary_projector_ref, cfg.neumann),
            declare.config.targetPoint(dirichlet_position_ref, cfg.dirichlet_position),
        });

        const disk_wick: []const wick.Rule = &disk_wick_storage;
        const disk_zero_modes: []const zero_mode.Rule = &disk_zero_storage;
        const config_entries = &config_storage;
    };
}

test "free-boson schema builders return opaque local tokens" {
    const testing = std.testing;
    const X = freeBoson(.{ .dimension = 10 });

    var local = try X.local(testing.allocator);
    defer local.deinit();

    const mu = try local.index("mu");
    const k = try local.momentum("k");
    const z = try local.coord("z");
    const zbar = try local.coord("zbar");
    const dx = try X.op.dX(&local, mu, 2, z);
    const exp = try X.op.expX(&local, k, z, zbar);
    const ops = try local.ops(.{ dx, exp });

    try testing.expect(@typeInfo(@typeInfo(@TypeOf(dx)).pointer.child) == .@"opaque");
    try testing.expect(@typeInfo(@typeInfo(@TypeOf(exp)).pointer.child) == .@"opaque");
    try testing.expect(@typeInfo(@typeInfo(@TypeOf(ops)).pointer.child) == .@"opaque");
}

test "free-boson boundary schema builders return opaque local tokens" {
    const testing = std.testing;

    var local = try Local.init(testing.allocator);
    defer local.deinit();

    const mu = try local.index("mu");
    const k = try local.momentum("k");
    const y = try local.boundaryCoord("y");
    const dx = try FreeBosonBoundaryOp.dXBoundary(&local, mu, 3, y);
    const exp = try FreeBosonBoundaryOp.expXBoundary(&local, k, y);
    const ops = try local.ops(.{ dx, exp });

    try testing.expect(@typeInfo(@typeInfo(@TypeOf(dx)).pointer.child) == .@"opaque");
    try testing.expect(@typeInfo(@typeInfo(@TypeOf(exp)).pointer.child) == .@"opaque");
    try testing.expect(@typeInfo(@typeInfo(@TypeOf(ops)).pointer.child) == .@"opaque");
}
