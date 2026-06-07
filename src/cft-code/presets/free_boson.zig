const std = @import("std");
const shared = @import("shared.zig");

const operators = @import("../expressions/operators.zig");
const kernel = @import("../kernel.zig");
const Handle = shared.Handle;
const RuleScalar = shared.RuleScalar;
const CorrelatorConfig = shared.CorrelatorConfig;
const BoundaryExtension = shared.BoundaryExtension;
const Local = shared.Local;
const wick = shared.wick;
const zero_mode = shared.zero_mode;

const namespace = "free_boson";
const scalars = shared.scalars;
const alpha_prime_atom = scalars.atom(namespace, "alpha_prime");
const k_disk_atom = scalars.atom(namespace, "K_D2");
const neumann_projector_ref = shared.configRef(namespace, "neumann_projector");
const dirichlet_projector_ref = shared.configRef(namespace, "dirichlet_projector");
const bulk_boundary_projector_ref = shared.configRef(namespace, "bulk_boundary_projector");
const dirichlet_position_ref = shared.configRef(namespace, "dirichlet_position");
const chan_paton_ref = shared.configRef(namespace, "chan_paton");
const target_dimension_ref = shared.configRef(namespace, "target_dimension");

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
};

fn kind(comptime family: Family) operators.OperatorKindId {
    return shared.familyKind(namespace, family);
}

fn zeroSector(comptime sector: ZeroSector) zero_mode.Sector {
    return shared.sectorId(namespace, sector);
}

fn rawToken(value: anytype) u32 {
    return @intFromEnum(value);
}

fn token(comptime T: type, id: u32) T {
    return @enumFromInt(if (id == 0) 1 else id);
}

fn coordVariable(coord: Handle.Coord) u32 {
    return rawToken(coord);
}

fn singleInsertion(z: Handle.Coord, derivatives: u8) operators.OperatorInsertion {
    return .{ .single = .{
        .position = coordVariable(z),
        .derivatives = derivatives,
    } };
}

fn pairInsertion(z: Handle.Coord, zbar: Handle.Coord) operators.OperatorInsertion {
    return .{ .pair = .{
        .holomorphic_position = coordVariable(z),
        .antiholomorphic_position = coordVariable(zbar),
        .holomorphic_derivatives = 0,
        .antiholomorphic_derivatives = 0,
    } };
}

fn boundaryCoord(y: Handle.BoundaryCoord) Handle.Coord {
    return token(Handle.Coord, rawToken(y));
}

fn freeBosonPattern(comptime family: Family, comptime support: wick.Support) wick.Pattern {
    return wick.pattern(kind(family), support);
}

fn dXPattern() wick.Pattern {
    return freeBosonPattern(.d_x, .holomorphic);
}

fn dXtPattern() wick.Pattern {
    return freeBosonPattern(.d_xt, .antiholomorphic);
}

fn expXPattern() wick.Pattern {
    return freeBosonPattern(.exp_x, .bulk_pair);
}

fn profilePattern() wick.Pattern {
    return freeBosonPattern(.profile_x, .bulk_pair);
}

fn dXBoundaryPattern() wick.Pattern {
    return freeBosonPattern(.d_x_boundary, .boundary);
}

fn expXBoundaryPattern() wick.Pattern {
    return freeBosonPattern(.exp_x_boundary, .boundary);
}

fn profileBoundaryPattern() wick.Pattern {
    return freeBosonPattern(.profile_x_boundary, .boundary);
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

fn polynomialProfileId(point: Handle.TargetPoint, comptime terms: []const Handle.PolynomialProfileTerm) u32 {
    var hash = rawToken(point) ^ 0x9e37_79b9;
    inline for (terms) |term| {
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

/// FreeBosonConfig declares a noncompact D-dimensional free boson preset.
pub const FreeBosonConfig = struct {
    dimension: u16,
    alpha_prime: shared.ScalarAtom = alpha_prime_atom,
    zero_mode_normalization: RuleScalar = .one,
};

/// freeBoson builds the generated preset type for a noncompact free-boson CFT.
pub fn freeBoson(comptime cfg: FreeBosonConfig) type {
    return struct {
        /// is_free_boson_preset identifies this generated type for composition.
        pub const is_free_boson_preset = true;
        /// op exposes free-boson local operator builders.
        pub const op = FreeBosonOp;
        /// profile exposes profile-presentation builders.
        pub const profile = ProfileOp;
        /// target exposes deterministic target-space tokens for preset data.
        pub const target = TargetSpace;
        /// config exposes named correlator configs for this preset.
        pub const config = FreeBosonCorrelatorConfig(cfg);
        /// rules exposes the preset-authored Wick rule templates.
        pub const rules = FreeBosonRules(cfg);

        /// local constructs a label-preserving local-operator builder.
        pub fn local(allocator: std.mem.Allocator) Local {
            return Local.init(allocator);
        }

        /// correlator streams rule matches for free-boson insertions.
        pub fn correlator(config_ptr: *const CorrelatorConfig, ops: kernel.Call.MultiOp, sink: anytype) !void {
            return shared.streamCorrelator(config_ptr, ops, sink);
        }
    };
}

const FreeBosonOp = struct {
    /// X builds an explicit bulk free-boson field insertion.
    pub fn X(local: *Local, mu: Handle.Index, z: Handle.Coord, zbar: Handle.Coord) !kernel.Call.LocalOp {
        return local.op(kind(.x), pairInsertion(z, zbar), &.{Local.symbol(mu)});
    }

    /// dX builds a holomorphic derivative field insertion.
    pub fn dX(local: *Local, mu: Handle.Index, n: u8, z: Handle.Coord) !kernel.Call.LocalOp {
        return local.op(kind(.d_x), singleInsertion(z, n), &.{Local.symbol(mu)});
    }

    /// dXt builds an antiholomorphic derivative field insertion.
    pub fn dXt(local: *Local, mu: Handle.Index, n: u8, zbar: Handle.Coord) !kernel.Call.LocalOp {
        return local.op(kind(.d_xt), singleInsertion(zbar, n), &.{Local.symbol(mu)});
    }

    /// expX builds a normal-ordered plane-wave insertion.
    pub fn expX(local: *Local, k: Handle.Momentum, z: Handle.Coord, zbar: Handle.Coord) !kernel.Call.LocalOp {
        return local.op(kind(.exp_x), pairInsertion(z, zbar), &.{Local.symbol(k)});
    }

    /// profile builds a target-space profile insertion.
    pub fn profile(local: *Local, f: Handle.Profile, z: Handle.Coord, zbar: Handle.Coord) !kernel.Call.LocalOp {
        return local.op(kind(.profile_x), pairInsertion(z, zbar), &.{Local.symbol(f)});
    }

    /// profileVector builds a vector-valued target-space profile insertion.
    pub fn profileVector(local: *Local, f: Handle.Profile, nu: Handle.Index, z: Handle.Coord, zbar: Handle.Coord) !kernel.Call.LocalOp {
        return local.op(kind(.profile_x), pairInsertion(z, zbar), &.{ Local.symbol(f), Local.symbol(nu) });
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
    pub fn polynomialRnc(point: Handle.TargetPoint, comptime terms: []const Handle.PolynomialProfileTerm) Handle.Profile {
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

fn bulkToBoundaryHolomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .holomorphic), wick.coord(.right, .position));
}

fn bulkToBoundaryAntiholomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .antiholomorphic), wick.coord(.right, .position));
}

fn freeBosonDxDx(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(alpha, 2), .{ .metric = .{
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, holomorphicDifference(), -2, .{ .include_left = true, .include_right = true });
}

fn freeBosonDxtDxt(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(alpha, 2), .{ .metric = .{
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, antiholomorphicDifference(), -2, .{ .include_left = true, .include_right = true });
}

fn freeBosonDxExpX(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(scalars.neg(scalars.i(alpha)), 2), .{ .momentum_index = .{
        .momentum = wick.label(.right, 0),
        .index = wick.label(.left, 0),
    } }, holomorphicDifference(), -1, .{ .include_left = true });
}

fn freeBosonDxProfile(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedActionPole(scalars.div(scalars.neg(alpha), 2), .none, holomorphicDifference(), -1, .{ .include_left = true }, &.{
        wick.profileDerivative(wick.label(.right, 0), wick.label(.left, 0)),
    });
}

fn freeBosonDxtExpX(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(scalars.neg(scalars.i(alpha)), 2), .{ .momentum_index = .{
        .momentum = wick.label(.right, 0),
        .index = wick.label(.left, 0),
    } }, antiholomorphicDifference(), -1, .{ .include_left = true });
}

fn freeBosonDxtProfile(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedActionPole(scalars.div(scalars.neg(alpha), 2), .none, antiholomorphicDifference(), -1, .{ .include_left = true }, &.{
        wick.profileDerivative(wick.label(.right, 0), wick.label(.left, 0)),
    });
}

fn freeBosonExpXExpX(comptime alpha: RuleScalar) wick.Expr {
    return wick.greenExponential(scalars.div(alpha, 2), .{ .momentum_pair = .{
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, bulkHolomorphicDifference());
}

fn sphereWickStorage(comptime alpha: RuleScalar) [7]wick.Rule {
    return [_]wick.Rule{
        wick.rule(dXPattern(), dXPattern(), freeBosonDxDx(alpha)),
        wick.rule(dXtPattern(), dXtPattern(), freeBosonDxtDxt(alpha)),
        wick.rule(dXPattern(), expXPattern(), freeBosonDxExpX(alpha)),
        wick.rule(dXtPattern(), expXPattern(), freeBosonDxtExpX(alpha)),
        wick.rule(dXPattern(), profilePattern(), freeBosonDxProfile(alpha)),
        wick.rule(dXtPattern(), profilePattern(), freeBosonDxtProfile(alpha)),
        wick.rule(expXPattern(), expXPattern(), freeBosonExpXExpX(alpha)),
    };
}

fn sphereZeroStorage(comptime cfg: FreeBosonConfig) [1]zero_mode.Rule {
    return [_]zero_mode.Rule{
        zero_mode.rule(zeroSector(.bulk), .{ .free_boson_constant_mode = .{
            .exp_kind_ids = &.{kind(.exp_x)},
            .profile_kind_ids = &.{kind(.profile_x)},
            .normalization = .{
                .scalar = cfg.zero_mode_normalization,
                .two_pi_power = .{ .target_dimension = target_dimension_ref },
            },
        } }),
    };
}

fn FreeBosonRules(comptime cfg: FreeBosonConfig) type {
    const alpha = scalars.atomScalar(cfg.alpha_prime);
    return struct {
        const sphere_wick_storage = sphereWickStorage(alpha);

        /// sphere_wick lists the primitive free-boson Wick rules on the sphere.
        pub const sphere_wick: []const wick.Rule = &sphere_wick_storage;
    };
}

fn FreeBosonCorrelatorConfig(comptime cfg: FreeBosonConfig) type {
    const rules = FreeBosonRules(cfg);
    return struct {
        const sphere_zero_storage = sphereZeroStorage(cfg);
        const sphere_wick_index_storage = shared.wickRuleIndexStorage(rules.sphere_wick);

        /// sphere selects free-boson sphere Wick and zero-mode rules.
        pub const sphere = CorrelatorConfig{
            .wick_rules = rules.sphere_wick,
            .wick_rule_index = &sphere_wick_index_storage,
            .zero_modes = &sphere_zero_storage,
            .config_entries = &.{
                .{ .id = target_dimension_ref, .value = .{ .target_dimension = cfg.dimension } },
            },
        };
    };
}

/// FreeBosonBoundaryConfig declares Neumann and Dirichlet data for a brane.
pub const FreeBosonBoundaryConfig = struct {
    neumann: Handle.TensorProjector,
    dirichlet: Handle.TensorProjector,
    dirichlet_position: Handle.TargetPoint,
    alpha_prime: shared.ScalarAtom = alpha_prime_atom,
    zero_mode_normalization: RuleScalar = scalars.atomScalar(k_disk_atom),
    chan_paton: ?Handle.BoundaryStack = null,
};

const FreeBosonBoundaryOp = struct {
    /// dXBoundary builds stringbook's holomorphic boundary limit of dX.
    pub fn dXBoundary(local: *Local, mu: Handle.Index, n: u8, y: Handle.BoundaryCoord) !kernel.Call.LocalOp {
        return local.op(kind(.d_x_boundary), singleInsertion(boundaryCoord(y), n), &.{Local.symbol(mu)});
    }

    /// expXBoundary builds a Neumann boundary plane-wave insertion.
    pub fn expXBoundary(local: *Local, k: Handle.Momentum, y: Handle.BoundaryCoord) !kernel.Call.LocalOp {
        return local.op(kind(.exp_x_boundary), singleInsertion(boundaryCoord(y), 0), &.{Local.symbol(k)});
    }

    /// profileBoundary builds a boundary profile insertion.
    pub fn profileBoundary(local: *Local, f: Handle.Profile, y: Handle.BoundaryCoord) !kernel.Call.LocalOp {
        return local.op(kind(.profile_x_boundary), singleInsertion(boundaryCoord(y), 0), &.{Local.symbol(f)});
    }

    /// profileBoundaryVector builds a vector-valued boundary profile insertion.
    pub fn profileBoundaryVector(local: *Local, f: Handle.Profile, nu: Handle.Index, y: Handle.BoundaryCoord) !kernel.Call.LocalOp {
        return local.op(kind(.profile_x_boundary), singleInsertion(boundaryCoord(y), 0), &.{ Local.symbol(f), Local.symbol(nu) });
    }
};

/// boundaryExtension declares the Neumann/Dirichlet free-boson boundary extension.
pub fn boundaryExtension(comptime cfg: FreeBosonBoundaryConfig) BoundaryExtension {
    const data = FreeBosonBoundaryData(cfg);
    return .{
        .kind = shared.extensionKind("free_boson_boundary"),
        .op = FreeBosonBoundaryOp,
        .wick_rules = data.disk_wick,
        .zero_modes = data.disk_zero_modes,
        .config_entries = data.config_entries,
    };
}

fn boundaryFreeBosonDxDx(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(alpha, .{ .projector_metric = .{
        .projector = .{ .config = neumann_projector_ref },
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, holomorphicDifference(), -2, .{ .include_left = true, .include_right = true });
}

fn boundaryFreeBosonDxExpX(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.neg(scalars.i(alpha)), .{ .projector_momentum_index = .{
        .projector = .{ .config = neumann_projector_ref },
        .momentum = wick.label(.right, 0),
        .index = wick.label(.left, 0),
    } }, holomorphicDifference(), -1, .{ .include_left = true });
}

fn boundaryFreeBosonDxProfile(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedActionPole(scalars.neg(alpha), .none, holomorphicDifference(), -1, .{ .include_left = true }, &.{
        wick.projectedProfileDerivative(.{ .config = neumann_projector_ref }, wick.label(.right, 0), wick.label(.left, 0)),
    });
}

fn boundaryFreeBosonExpXExpX(comptime alpha: RuleScalar) wick.Expr {
    return wick.greenExponential(alpha, .{ .projector_momentum_pair = .{
        .projector = .{ .config = neumann_projector_ref },
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, holomorphicDifference());
}

fn mixedFreeBosonDxDxBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(alpha, 2), .{ .projector_metric = .{
        .projector = .{ .config = bulk_boundary_projector_ref },
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, bulkToBoundaryHolomorphicDifference(), -2, .{ .include_left = true, .include_right = true });
}

fn mixedFreeBosonDxtDxBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(alpha, 2), .{ .projector_metric = .{
        .projector = .{ .config = bulk_boundary_projector_ref },
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, bulkToBoundaryAntiholomorphicDifference(), -2, .{ .include_left = true, .include_right = true });
}

fn mixedFreeBosonDxExpXBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(scalars.neg(scalars.i(alpha)), 2), .{ .projector_momentum_index = .{
        .projector = .{ .config = bulk_boundary_projector_ref },
        .momentum = wick.label(.right, 0),
        .index = wick.label(.left, 0),
    } }, bulkToBoundaryHolomorphicDifference(), -1, .{ .include_left = true });
}

fn mixedFreeBosonDxProfileBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedActionPole(scalars.div(scalars.neg(alpha), 2), .none, bulkToBoundaryHolomorphicDifference(), -1, .{ .include_left = true }, &.{
        wick.projectedProfileDerivative(.{ .config = bulk_boundary_projector_ref }, wick.label(.right, 0), wick.label(.left, 0)),
    });
}

fn mixedFreeBosonDxtExpXBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedPole(scalars.div(scalars.neg(scalars.i(alpha)), 2), .{ .projector_momentum_index = .{
        .projector = .{ .config = bulk_boundary_projector_ref },
        .momentum = wick.label(.right, 0),
        .index = wick.label(.left, 0),
    } }, bulkToBoundaryAntiholomorphicDifference(), -1, .{ .include_left = true });
}

fn mixedFreeBosonDxtProfileBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.differentiatedActionPole(scalars.div(scalars.neg(alpha), 2), .none, bulkToBoundaryAntiholomorphicDifference(), -1, .{ .include_left = true }, &.{
        wick.projectedProfileDerivative(.{ .config = bulk_boundary_projector_ref }, wick.label(.right, 0), wick.label(.left, 0)),
    });
}

fn mixedFreeBosonExpXExpXBoundary(comptime alpha: RuleScalar) wick.Expr {
    return wick.greenExponential(scalars.div(alpha, 2), .{ .projector_momentum_pair = .{
        .projector = .{ .config = bulk_boundary_projector_ref },
        .left = wick.label(.left, 0),
        .right = wick.label(.right, 0),
    } }, bulkToBoundaryHolomorphicDifference());
}

fn diskWickStorage(comptime alpha: RuleScalar) [11]wick.Rule {
    return [_]wick.Rule{
        wick.rule(dXBoundaryPattern(), dXBoundaryPattern(), boundaryFreeBosonDxDx(alpha)),
        wick.rule(dXBoundaryPattern(), expXBoundaryPattern(), boundaryFreeBosonDxExpX(alpha)),
        wick.rule(dXBoundaryPattern(), profileBoundaryPattern(), boundaryFreeBosonDxProfile(alpha)),
        wick.rule(expXBoundaryPattern(), expXBoundaryPattern(), boundaryFreeBosonExpXExpX(alpha)),
        wick.rule(dXPattern(), dXBoundaryPattern(), mixedFreeBosonDxDxBoundary(alpha)),
        wick.rule(dXtPattern(), dXBoundaryPattern(), mixedFreeBosonDxtDxBoundary(alpha)),
        wick.rule(dXPattern(), expXBoundaryPattern(), mixedFreeBosonDxExpXBoundary(alpha)),
        wick.rule(dXtPattern(), expXBoundaryPattern(), mixedFreeBosonDxtExpXBoundary(alpha)),
        wick.rule(dXPattern(), profileBoundaryPattern(), mixedFreeBosonDxProfileBoundary(alpha)),
        wick.rule(dXtPattern(), profileBoundaryPattern(), mixedFreeBosonDxtProfileBoundary(alpha)),
        wick.rule(expXPattern(), expXBoundaryPattern(), mixedFreeBosonExpXExpXBoundary(alpha)),
    };
}

fn diskZeroStorage(comptime cfg: FreeBosonBoundaryConfig) [1]zero_mode.Rule {
    return [_]zero_mode.Rule{
        zero_mode.rule(zeroSector(.boundary), .{ .free_boson_constant_mode = .{
            .integration_projector = neumann_projector_ref,
            .fixed_projector = dirichlet_projector_ref,
            .fixed_position = dirichlet_position_ref,
            .exp_kind_ids = &.{ kind(.exp_x), kind(.exp_x_boundary) },
            .profile_kind_ids = &.{ kind(.profile_x), kind(.profile_x_boundary) },
            .normalization = .{
                .scalar = cfg.zero_mode_normalization,
                .two_pi_power = .{ .projector_rank = neumann_projector_ref },
            },
        } }),
    };
}

fn FreeBosonBoundaryData(comptime cfg: FreeBosonBoundaryConfig) type {
    const alpha = scalars.atomScalar(cfg.alpha_prime);
    return struct {
        const disk_wick_storage = diskWickStorage(alpha);
        const disk_zero_storage = diskZeroStorage(cfg);
        const config_storage = if (cfg.chan_paton) |stack| [_]shared.ConfigEntry{
            .{ .id = neumann_projector_ref, .value = .{ .tensor_projector = cfg.neumann } },
            .{ .id = dirichlet_projector_ref, .value = .{ .tensor_projector = cfg.dirichlet } },
            .{ .id = bulk_boundary_projector_ref, .value = .{ .tensor_projector = cfg.neumann } },
            .{ .id = dirichlet_position_ref, .value = .{ .target_point = cfg.dirichlet_position } },
            .{ .id = chan_paton_ref, .value = .{ .boundary_stack = stack } },
        } else [_]shared.ConfigEntry{
            .{ .id = neumann_projector_ref, .value = .{ .tensor_projector = cfg.neumann } },
            .{ .id = dirichlet_projector_ref, .value = .{ .tensor_projector = cfg.dirichlet } },
            .{ .id = bulk_boundary_projector_ref, .value = .{ .tensor_projector = cfg.neumann } },
            .{ .id = dirichlet_position_ref, .value = .{ .target_point = cfg.dirichlet_position } },
        };

        /// disk_wick lists boundary and mixed free-boson Wick rules on the disk.
        pub const disk_wick: []const wick.Rule = &disk_wick_storage;
        /// disk_zero_modes lists free-boson constant-mode rules on the disk.
        pub const disk_zero_modes: []const zero_mode.Rule = &disk_zero_storage;
        /// config_entries lists typed Neumann, Dirichlet, and Chan-Paton boundary data.
        pub const config_entries: []const shared.ConfigEntry = &config_storage;
    };
}
