const std = @import("std");
const shared = @import("shared.zig");
const declare = shared.declare;

const operators = @import("../expressions/operators.zig");
const Handle = shared.Handle;
const Builder = *shared.Local;
const Operator = *shared.LocalOperator;
const Spec = declare.Spec;
const wick = declare.wick;
const zero_mode = declare.zero_mode;

const namespace = "eta_xi";

const Family = enum {
    eta,
    xi,
    etat,
    xit,
};

const ZeroSector = enum {
    sphere,
    torus,
};

fn kind(comptime family: Family) operators.OperatorKindId {
    return declare.familyKind(namespace, family);
}

fn zeroSector(comptime sector: ZeroSector) zero_mode.Sector {
    return declare.sectorId(namespace, sector);
}

const EtaXiSphereConfig = struct {
    include_antiholomorphic_copy: bool = true,
};

/// etaXiSphere builds the generated preset type for the sphere eta-xi system.
pub fn etaXiSphere(comptime cfg: EtaXiSphereConfig) type {
    return struct {
        /// op exposes eta-xi local operator builders.
        pub const op = EtaXiSphereOp(cfg.include_antiholomorphic_copy);
        /// config exposes named correlator configs for this preset.
        pub const config = EtaXiSphereCorrelatorConfig(cfg);
        /// text exposes bounded result-inspection sinks.
        pub const text = shared.text;
        /// local constructs a label-preserving local-operator builder.
        pub fn local(allocator: std.mem.Allocator) !Builder {
            return shared.Local.init(allocator);
        }

        /// correlator streams rule matches for eta-xi insertions.
        pub fn correlator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
            return shared.streamCorrelator(config_ptr, ops, sink);
        }
    };
}

fn EtaXiSphereOp(comptime include_antiholomorphic_copy: bool) type {
    const Holomorphic = struct {
        /// eta builds a holomorphic eta insertion.
        pub fn eta(local: anytype, n: u8, z: Handle.Coord) !Operator {
            return declare.operatorBuilder(etaXiOperator(.eta)).single(local, z, n, .{});
        }

        /// xi builds a holomorphic xi insertion.
        pub fn xi(local: anytype, n: u8, z: Handle.Coord) !Operator {
            return declare.operatorBuilder(etaXiOperator(.xi)).single(local, z, n, .{});
        }
    };

    if (!include_antiholomorphic_copy) return Holomorphic;

    return struct {
        /// eta builds a holomorphic eta insertion.
        pub const eta = Holomorphic.eta;
        /// xi builds a holomorphic xi insertion.
        pub const xi = Holomorphic.xi;

        /// etat builds an antiholomorphic eta insertion.
        pub fn etat(local: anytype, n: u8, zbar: Handle.Coord) !Operator {
            return declare.operatorBuilder(etaXiOperator(.etat)).single(local, zbar, n, .{});
        }

        /// xit builds an antiholomorphic xi insertion.
        pub fn xit(local: anytype, n: u8, zbar: Handle.Coord) !Operator {
            return declare.operatorBuilder(etaXiOperator(.xit)).single(local, zbar, n, .{});
        }
    };
}

fn holomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .position), wick.coord(.right, .position));
}

fn antiholomorphicDifference() wick.CoordinateDifference {
    return wick.difference(wick.coord(.left, .position), wick.coord(.right, .position));
}

fn etaXi() wick.Expr {
    return wick.differentiatedPole(.one, .none, holomorphicDifference(), -1, .{ .include_left = true, .include_right = true });
}

fn etatXit() wick.Expr {
    return wick.differentiatedPole(.one, .none, antiholomorphicDifference(), -1, .{ .include_left = true, .include_right = true });
}

fn etaXiTorus() wick.Expr {
    return wick.expr(&.{wick.term(&.{wick.scalar(.one)}, &.{wick.differentiatedGreenKernel("elliptic_prime_form_log_derivative", holomorphicDifference(), .{ .include_left = true, .include_right = true })}, &.{.none})});
}

fn etatXitTorus() wick.Expr {
    return wick.expr(&.{wick.term(&.{wick.scalar(.one)}, &.{wick.differentiatedGreenKernel("elliptic_prime_form_log_derivative", antiholomorphicDifference(), .{ .include_left = true, .include_right = true })}, &.{.none})});
}

fn sphereZeroSpec(comptime cfg: EtaXiSphereConfig) if (cfg.include_antiholomorphic_copy) [2]Spec.ZeroModeRule else [1]Spec.ZeroModeRule {
    const holomorphic = Spec.ZeroModeRule{ .sector = zeroSector(.sphere), .expr = .{ .eta_xi_zero_mode = .{
        .support = .sphere_holomorphic,
        .xi_kind_ids = &.{kind(.xi)},
        .normalization = .one,
    } } };
    if (!cfg.include_antiholomorphic_copy) return [_]Spec.ZeroModeRule{holomorphic};
    return [_]Spec.ZeroModeRule{
        holomorphic,
        .{ .sector = zeroSector(.sphere), .expr = .{ .eta_xi_zero_mode = .{
            .support = .sphere_antiholomorphic,
            .xi_kind_ids = &.{kind(.xit)},
            .normalization = .one,
        } } },
    };
}

fn sphereZeroStorage(comptime cfg: EtaXiSphereConfig) if (cfg.include_antiholomorphic_copy) [2]zero_mode.Rule else [1]zero_mode.Rule {
    const spec = sphereZeroSpec(cfg);
    return Spec.zeroModeRules(&spec);
}

fn torusZeroSpec(comptime cfg: EtaXiSphereConfig) if (cfg.include_antiholomorphic_copy) [2]Spec.ZeroModeRule else [1]Spec.ZeroModeRule {
    const holomorphic = Spec.ZeroModeRule{ .sector = zeroSector(.torus), .expr = .{ .eta_xi_zero_mode = .{
        .support = .torus_holomorphic,
        .xi_kind_ids = &.{kind(.xi)},
        .normalization = .one,
    } } };
    if (!cfg.include_antiholomorphic_copy) return [_]Spec.ZeroModeRule{holomorphic};
    return [_]Spec.ZeroModeRule{
        holomorphic,
        .{ .sector = zeroSector(.torus), .expr = .{ .eta_xi_zero_mode = .{
            .support = .torus_antiholomorphic,
            .xi_kind_ids = &.{kind(.xit)},
            .normalization = .one,
        } } },
    };
}

fn torusZeroStorage(comptime cfg: EtaXiSphereConfig) if (cfg.include_antiholomorphic_copy) [2]zero_mode.Rule else [1]zero_mode.Rule {
    const spec = torusZeroSpec(cfg);
    return Spec.zeroModeRules(&spec);
}

const sphere_holomorphic_operator_spec = [_]Spec.Operator{
    .{ .name = "eta", .kind = kind(.eta), .support = .holomorphic, .insertion = .single, .statistics = .fermionic },
    .{ .name = "xi", .kind = kind(.xi), .support = .holomorphic, .insertion = .single, .statistics = .fermionic, .zero_mode_consumable = true },
};

const sphere_full_operator_spec = sphere_holomorphic_operator_spec ++ [_]Spec.Operator{
    .{ .name = "etat", .kind = kind(.etat), .support = .antiholomorphic, .insertion = .single, .statistics = .fermionic },
    .{ .name = "xit", .kind = kind(.xit), .support = .antiholomorphic, .insertion = .single, .statistics = .fermionic, .zero_mode_consumable = true },
};

const sphere_holomorphic_wick_spec = [_]Spec.WickRule{
    .{ .left = kind(.eta), .right = kind(.xi), .expr = etaXi() },
};

const sphere_full_wick_spec = sphere_holomorphic_wick_spec ++ [_]Spec.WickRule{
    .{ .left = kind(.etat), .right = kind(.xit), .expr = etatXit() },
};

const sphere_holomorphic_wick_storage = Spec.wickRules(&sphere_holomorphic_wick_spec, &sphere_holomorphic_operator_spec);
const sphere_full_wick_storage = Spec.wickRules(&sphere_full_wick_spec, &sphere_full_operator_spec);

const sphere_holomorphic_fermion_storage = Spec.fermionKinds(&sphere_holomorphic_operator_spec);
const sphere_full_fermion_storage = Spec.fermionKinds(&sphere_full_operator_spec);

const sphere_holomorphic_zero_spec = sphereZeroSpec(.{ .include_antiholomorphic_copy = false });
const sphere_full_zero_spec = sphereZeroSpec(.{});

const torus_holomorphic_wick_spec = [_]Spec.WickRule{
    .{ .left = kind(.eta), .right = kind(.xi), .expr = etaXiTorus(), .coordinate_kernels = &.{.elliptic_prime_form_log_derivative} },
};

const torus_full_wick_spec = torus_holomorphic_wick_spec ++ [_]Spec.WickRule{
    .{ .left = kind(.etat), .right = kind(.xit), .expr = etatXitTorus(), .coordinate_kernels = &.{.elliptic_prime_form_log_derivative} },
};

const torus_holomorphic_wick_storage = Spec.wickRules(&torus_holomorphic_wick_spec, &sphere_holomorphic_operator_spec);
const torus_full_wick_storage = Spec.wickRules(&torus_full_wick_spec, &sphere_full_operator_spec);

const torus_holomorphic_zero_spec = torusZeroSpec(.{ .include_antiholomorphic_copy = false });
const torus_full_zero_spec = torusZeroSpec(.{});

fn etaXiSphereSpec(comptime include_antiholomorphic_copy: bool) Spec.Theory {
    return .{
        .operators = if (include_antiholomorphic_copy) &sphere_full_operator_spec else &sphere_holomorphic_operator_spec,
        .wick_rules = if (include_antiholomorphic_copy) &sphere_full_wick_spec else &sphere_holomorphic_wick_spec,
        .zero_modes = if (include_antiholomorphic_copy) &sphere_full_zero_spec else &sphere_holomorphic_zero_spec,
    };
}

const torus_draft_spec = Spec.Theory{
    .surface = .{
        .kind = .torus,
        .coordinate_model = .elliptic,
        .modular_parameters = &.{"tau"},
        .source = .stringbook,
    },
    .operators = &sphere_full_operator_spec,
    .wick_rules = &torus_full_wick_spec,
    .zero_modes = &torus_full_zero_spec,
};

fn etaXiOperator(comptime family: Family) Spec.Operator {
    const kind_id = kind(family);
    inline for (sphere_full_operator_spec) |operator| {
        if (operator.kind == kind_id) return operator;
    }
    @compileError("missing eta-xi operator spec");
}

fn assertSphereSpec(comptime include_antiholomorphic_copy: bool, comptime wick_count: usize, comptime zero_count: usize, comptime fermion_count: usize) void {
    const spec = etaXiSphereSpec(include_antiholomorphic_copy);
    if (spec.wick_rules.len != wick_count) @compileError("eta-xi sphere spec Wick count does not match lowered rules");
    if (spec.zero_modes.len != zero_count) @compileError("eta-xi sphere spec zero-mode count does not match lowered rules");
    if (spec.operators.len != fermion_count) @compileError("eta-xi sphere spec fermion coverage does not match lowered rules");
}

fn assertTorusDraftSpec() void {
    if (torus_draft_spec.surface.kind != .torus) @compileError("eta-xi torus draft spec surface kind is incomplete");
    if (torus_draft_spec.surface.coordinate_model != .elliptic) @compileError("eta-xi torus draft spec coordinate model is incomplete");
    if (torus_draft_spec.surface.modular_parameters.len != 1) @compileError("eta-xi torus draft spec modular metadata is incomplete");
    if (torus_draft_spec.surface.source != .stringbook) @compileError("eta-xi torus draft spec source convention is incomplete");
    if (torus_draft_spec.operators.len != sphere_full_operator_spec.len) @compileError("eta-xi torus draft spec operator metadata is incomplete");
    if (torus_draft_spec.wick_rules.len != sphere_full_wick_spec.len) @compileError("eta-xi torus draft spec Wick metadata is incomplete");
    if (Spec.wickCoordinateKernelCount(torus_draft_spec.wick_rules, .elliptic_prime_form_log_derivative) != 2) @compileError("eta-xi torus draft spec prime-form log-derivative metadata is incomplete");
    if (Spec.wickCoordinateKernelCount(torus_draft_spec.wick_rules, .elliptic_prime_form) != 0) @compileError("eta-xi torus draft spec uses the prime form instead of its log derivative");
    if (Spec.wickCoordinateKernelCount(torus_draft_spec.wick_rules, .rational_pole) != 0) @compileError("eta-xi torus draft spec still uses rational pole metadata");
    if (torus_draft_spec.zero_modes.len != 2) @compileError("eta-xi torus draft spec zero-mode metadata is incomplete");
    if (Spec.zeroModeConsumeKindCount(torus_draft_spec.zero_modes[0]) != 1) @compileError("eta-xi torus draft spec holomorphic zero-mode coverage is incomplete");
    if (Spec.zeroModeConsumeKindCount(torus_draft_spec.zero_modes[1]) != 1) @compileError("eta-xi torus draft spec antiholomorphic zero-mode coverage is incomplete");
}

fn EtaXiSphereRules(comptime include_antiholomorphic_copy: bool) type {
    const selected_wick = if (include_antiholomorphic_copy) sphere_full_wick_storage else sphere_holomorphic_wick_storage;
    const selected_torus_wick = if (include_antiholomorphic_copy) torus_full_wick_storage else torus_holomorphic_wick_storage;
    const selected_fermions = if (include_antiholomorphic_copy) sphere_full_fermion_storage else sphere_holomorphic_fermion_storage;
    return struct {
        const sphere_wick: []const wick.Rule = &selected_wick;
        const torus_wick: []const wick.Rule = &selected_torus_wick;
        const sphere_fermion_kinds: []const operators.OperatorKindId = &selected_fermions;
    };
}

fn EtaXiSphereCorrelatorConfig(comptime cfg: EtaXiSphereConfig) type {
    const rules = EtaXiSphereRules(cfg.include_antiholomorphic_copy);
    return struct {
        const sphere_zero_storage = sphereZeroStorage(cfg);
        const torus_zero_storage = torusZeroStorage(cfg);
        comptime {
            assertSphereSpec(cfg.include_antiholomorphic_copy, rules.sphere_wick.len, sphere_zero_storage.len, rules.sphere_fermion_kinds.len);
            assertTorusDraftSpec();
        }

        /// sphere selects eta-xi sphere Wick and xi zero-mode rules.
        pub const sphere = declare.correlatorConfig(.{
            .wick_rules = rules.sphere_wick,
            .zero_modes = &sphere_zero_storage,
            .fermion_kinds = rules.sphere_fermion_kinds,
        }){};

        /// torus selects eta-xi torus prime-form log-derivative Wick and xi zero-mode rules.
        pub const torus = declare.correlatorConfig(.{
            .wick_rules = rules.torus_wick,
            .zero_modes = &torus_zero_storage,
            .fermion_kinds = rules.sphere_fermion_kinds,
        }){};
    };
}
