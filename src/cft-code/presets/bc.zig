const std = @import("std");
const shared = @import("shared.zig");

const operators = @import("../expressions/operators.zig");
const kernel = @import("../kernel.zig");
const Handle = shared.Handle;
const CorrelatorConfig = shared.CorrelatorConfig;
const BoundaryExtension = shared.BoundaryExtension;
const Local = shared.Local;
const RuleScalar = shared.RuleScalar;
const wick = shared.wick;
const zero_mode = shared.zero_mode;

const namespace = "bc";

const Family = enum {
    b,
    c,
    bt,
    ct,
    b_boundary,
    c_boundary,
};

const ZeroSector = enum {
    sphere,
    disk,
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

fn boundaryCoord(y: Handle.BoundaryCoord) Handle.Coord {
    return token(Handle.Coord, rawToken(y));
}

fn bcPattern(comptime family: Family, comptime support: wick.Support) wick.Pattern {
    return wick.pattern(kind(family), support);
}

fn bPattern() wick.Pattern {
    return bcPattern(.b, .holomorphic);
}

fn cPattern() wick.Pattern {
    return bcPattern(.c, .holomorphic);
}

fn btPattern() wick.Pattern {
    return bcPattern(.bt, .antiholomorphic);
}

fn ctPattern() wick.Pattern {
    return bcPattern(.ct, .antiholomorphic);
}

fn bBoundaryPattern() wick.Pattern {
    return bcPattern(.b_boundary, .boundary);
}

fn cBoundaryPattern() wick.Pattern {
    return bcPattern(.c_boundary, .boundary);
}

/// BcSphereConfig declares the holomorphic bc system and optional antiholomorphic copy.
pub const BcSphereConfig = struct {
    include_antiholomorphic_copy: bool = true,
    top_form_normalization: RuleScalar = .one,
};

/// bcSphere builds the generated preset type for the sphere bc ghost CFT.
pub fn bcSphere(comptime cfg: BcSphereConfig) type {
    return struct {
        /// is_bc_sphere_preset identifies this generated type for composition.
        pub const is_bc_sphere_preset = true;

        /// op exposes bc ghost local operator builders.
        pub const op = BcSphereOp(cfg.include_antiholomorphic_copy);
        /// config exposes named correlator configs for this preset.
        pub const config = BcSphereCorrelatorConfig(cfg);
        /// rules exposes the preset-authored Wick rule templates.
        pub const rules = BcSphereRules(cfg.include_antiholomorphic_copy);

        /// local constructs a label-preserving local-operator builder.
        pub fn local(allocator: std.mem.Allocator) Local {
            return Local.init(allocator);
        }

        /// correlator streams rule matches for bc insertions.
        pub fn correlator(config_ptr: *const CorrelatorConfig, ops: kernel.Call.MultiOp, sink: anytype) !void {
            return shared.streamCorrelator(config_ptr, ops, sink);
        }
    };
}

fn BcSphereOp(comptime include_antiholomorphic_copy: bool) type {
    const Holomorphic = struct {
        /// b builds a holomorphic b-ghost insertion.
        pub fn b(local: *Local, n: u8, z: Handle.Coord) !kernel.Call.LocalOp {
            return local.op(kind(.b), singleInsertion(z, n), &.{});
        }

        /// c builds a holomorphic c-ghost insertion.
        pub fn c(local: *Local, n: u8, z: Handle.Coord) !kernel.Call.LocalOp {
            return local.op(kind(.c), singleInsertion(z, n), &.{});
        }
    };

    if (!include_antiholomorphic_copy) return Holomorphic;

    return struct {
        /// b builds a holomorphic b-ghost insertion.
        pub const b = Holomorphic.b;
        /// c builds a holomorphic c-ghost insertion.
        pub const c = Holomorphic.c;

        /// bt builds an antiholomorphic b-ghost insertion.
        pub fn bt(local: *Local, n: u8, zbar: Handle.Coord) !kernel.Call.LocalOp {
            return local.op(kind(.bt), singleInsertion(zbar, n), &.{});
        }

        /// ct builds an antiholomorphic c-ghost insertion.
        pub fn ct(local: *Local, n: u8, zbar: Handle.Coord) !kernel.Call.LocalOp {
            return local.op(kind(.ct), singleInsertion(zbar, n), &.{});
        }
    };
}

fn holomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .position), wick.coord(.right, .position));
}

fn antiholomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .position), wick.coord(.right, .position));
}

fn bcBC() wick.Expr {
    return wick.differentiatedPole(.one, .none, holomorphicDifference(), -1, .{ .include_left = true, .include_right = true });
}

fn bcBtCt() wick.Expr {
    return wick.differentiatedPole(.one, .none, antiholomorphicDifference(), -1, .{ .include_left = true, .include_right = true });
}

const sphere_holomorphic_wick_storage = [_]wick.Rule{
    wick.rule(bPattern(), cPattern(), bcBC()),
};

const sphere_full_wick_storage = sphere_holomorphic_wick_storage ++ [_]wick.Rule{
    wick.rule(btPattern(), ctPattern(), bcBtCt()),
};

fn sphereZeroStorage(comptime cfg: BcSphereConfig) if (cfg.include_antiholomorphic_copy) [2]zero_mode.Rule else [1]zero_mode.Rule {
    const holomorphic = zero_mode.rule(zeroSector(.sphere), .{ .bc_top_form = .{
        .support = .sphere_holomorphic,
        .c_kind_ids = &.{kind(.c)},
        .normalization = cfg.top_form_normalization,
    } });
    if (!cfg.include_antiholomorphic_copy) return [_]zero_mode.Rule{holomorphic};
    return [_]zero_mode.Rule{
        holomorphic,
        zero_mode.rule(zeroSector(.sphere), .{ .bc_top_form = .{
            .support = .sphere_antiholomorphic,
            .c_kind_ids = &.{kind(.ct)},
            .normalization = cfg.top_form_normalization,
        } }),
    };
}

fn BcSphereRules(comptime include_antiholomorphic_copy: bool) type {
    const selected_wick = if (include_antiholomorphic_copy) sphere_full_wick_storage else sphere_holomorphic_wick_storage;
    return struct {
        /// sphere_wick lists the primitive bc Wick rules on the sphere.
        pub const sphere_wick: []const wick.Rule = &selected_wick;
    };
}

fn BcSphereCorrelatorConfig(comptime cfg: BcSphereConfig) type {
    const rules = BcSphereRules(cfg.include_antiholomorphic_copy);
    return struct {
        const sphere_zero_storage = sphereZeroStorage(cfg);
        const sphere_wick_index_storage = shared.wickRuleIndexStorage(rules.sphere_wick);

        /// sphere selects bc sphere Wick and zero-mode rules.
        pub const sphere = CorrelatorConfig{
            .wick_rules = rules.sphere_wick,
            .wick_rule_index = &sphere_wick_index_storage,
            .zero_modes = &sphere_zero_storage,
        };
    };
}

/// BcDiskConfig declares the disk boundary extension for the bc ghost system.
pub const BcDiskConfig = struct {
    include_mixed_bulk_boundary: bool = true,
    top_form_normalization: RuleScalar = .one,
};

const BcDiskBoundaryOp = struct {
    /// bBoundary builds a boundary b-ghost insertion.
    pub fn bBoundary(local: *Local, n: u8, y: Handle.BoundaryCoord) !kernel.Call.LocalOp {
        return local.op(kind(.b_boundary), singleInsertion(boundaryCoord(y), n), &.{});
    }

    /// cBoundary builds a boundary c-ghost insertion.
    pub fn cBoundary(local: *Local, n: u8, y: Handle.BoundaryCoord) !kernel.Call.LocalOp {
        return local.op(kind(.c_boundary), singleInsertion(boundaryCoord(y), n), &.{});
    }
};

/// boundaryExtension declares boundary and mixed bulk-boundary bc rules on the disk.
pub fn boundaryExtension(comptime cfg: BcDiskConfig) BoundaryExtension {
    const data = BcDiskData(cfg);
    return .{
        .kind = shared.extensionKind("bc_disk"),
        .op = BcDiskBoundaryOp,
        .wick_rules = if (cfg.include_mixed_bulk_boundary) &disk_full_wick_storage else &disk_boundary_wick_storage,
        .zero_modes = data.disk_zero_modes,
    };
}

const disk_boundary_wick_storage = [_]wick.Rule{
    wick.rule(bBoundaryPattern(), cBoundaryPattern(), bcBC()),
};

const disk_full_wick_storage = disk_boundary_wick_storage ++ [_]wick.Rule{
    wick.rule(bPattern(), cBoundaryPattern(), bcBC()),
    wick.rule(cPattern(), bBoundaryPattern(), bcBC()),
    wick.rule(btPattern(), cBoundaryPattern(), bcBtCt()),
    wick.rule(ctPattern(), bBoundaryPattern(), bcBtCt()),
};

fn diskZeroStorage(comptime cfg: BcDiskConfig) [1]zero_mode.Rule {
    return [_]zero_mode.Rule{
        zero_mode.rule(zeroSector(.disk), .{ .bc_top_form = .{
            .support = .disk_doubled,
            .c_kind_ids = &.{ kind(.c), kind(.ct), kind(.c_boundary) },
            .normalization = cfg.top_form_normalization,
        } }),
    };
}

fn BcDiskData(comptime cfg: BcDiskConfig) type {
    return struct {
        const disk_zero_storage = diskZeroStorage(cfg);

        /// disk_zero_modes lists doubled chiral bc zero-mode rules on the disk.
        pub const disk_zero_modes: []const zero_mode.Rule = &disk_zero_storage;
    };
}
