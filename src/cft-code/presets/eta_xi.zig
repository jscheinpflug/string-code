const std = @import("std");
const basis_generation = @import("../basis-generation/basis-generation.zig");
const generated_fixtures = @import("../correlators/generated_fixtures.zig");
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
    quantum_schema: []const basis_generation.Quantum = &basis_generation.Preset.eta_xi_schema,
};

/// etaXiSphere builds the generated preset type for the sphere eta-xi system.
pub fn etaXiSphere(comptime cfg: EtaXiSphereConfig) type {
    return if (cfg.include_antiholomorphic_copy) GeneratedEtaXiFull else GeneratedEtaXi;
}

const GeneratedEtaXi = struct {
    const Sphere = generated_fixtures.EtaXiSphere;
    const Torus = generated_fixtures.EtaXiTorus;

    /// op exposes descriptor-generated eta-xi local operator builders.
    pub const op = struct {
        /// eta builds a holomorphic eta insertion.
        pub fn eta(builder: anytype, n: u8, z: Handle.Coord) !Operator {
            return Sphere.field("eta").localSingle(builder, z, n, .{});
        }

        /// xi builds a holomorphic xi insertion.
        pub fn xi(builder: anytype, n: u8, z: Handle.Coord) !Operator {
            return Sphere.field("xi").localSingle(builder, z, n, .{});
        }
    };
    /// config exposes descriptor-generated sphere and torus correlator configs.
    pub const config = struct {
        /// sphere selects descriptor-generated eta-xi sphere rules.
        pub const sphere = Sphere.config.sphere;
        /// torus selects descriptor-generated eta-xi torus rules.
        pub const torus = Torus.config.torus;
    };
    /// basis streams descriptor-generated compact eta-xi ghost mode words.
    pub const basis = Sphere.basis;
    /// text exposes bounded result-inspection sinks.
    pub const text = Sphere.text;

    /// local constructs a label-preserving local-operator builder.
    pub fn local(allocator: std.mem.Allocator) !Builder {
        return shared.Local.init(allocator);
    }

    /// correlator streams descriptor-generated rule matches for eta-xi insertions.
    pub fn correlator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
        return shared.streamCorrelator(config_ptr, ops, sink);
    }
};

const GeneratedEtaXiFull = struct {
    const Sphere = generated_fixtures.EtaXiSphereFull;
    const Torus = generated_fixtures.EtaXiTorusFull;

    /// op exposes descriptor-generated eta-xi local operator builders.
    pub const op = struct {
        /// eta builds a holomorphic eta insertion.
        pub fn eta(builder: anytype, n: u8, z: Handle.Coord) !Operator {
            return Sphere.field("eta").localSingle(builder, z, n, .{});
        }

        /// xi builds a holomorphic xi insertion.
        pub fn xi(builder: anytype, n: u8, z: Handle.Coord) !Operator {
            return Sphere.field("xi").localSingle(builder, z, n, .{});
        }

        /// etat builds an antiholomorphic eta insertion.
        pub fn etat(builder: anytype, n: u8, zbar: Handle.Coord) !Operator {
            return Sphere.field("etat").localSingle(builder, zbar, n, .{});
        }

        /// xit builds an antiholomorphic xi insertion.
        pub fn xit(builder: anytype, n: u8, zbar: Handle.Coord) !Operator {
            return Sphere.field("xit").localSingle(builder, zbar, n, .{});
        }
    };
    /// config exposes descriptor-generated sphere and torus correlator configs.
    pub const config = struct {
        /// sphere selects descriptor-generated eta-xi sphere rules.
        pub const sphere = Sphere.config.sphere;
        /// torus selects descriptor-generated eta-xi torus rules.
        pub const torus = Torus.config.torus;
    };
    /// basis streams descriptor-generated compact eta-xi ghost mode words.
    pub const basis = Sphere.basis;
    /// text exposes bounded result-inspection sinks.
    pub const text = Sphere.text;

    /// local constructs a label-preserving local-operator builder.
    pub fn local(allocator: std.mem.Allocator) !Builder {
        return shared.Local.init(allocator);
    }

    /// correlator streams descriptor-generated rule matches for eta-xi insertions.
    pub fn correlator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
        return shared.streamCorrelator(config_ptr, ops, sink);
    }
};

fn etaXiModeCapacity(comptime max_level_ticks: u32) usize {
    return 2 * max_level_ticks;
}

fn EtaXiBasis(comptime cfg: EtaXiSphereConfig) type {
    return struct {
        /// quantum_schema carries the one-slot eta-xi U(1) charge filter.
        pub const quantum_schema = cfg.quantum_schema;
        /// render_modes names compact oscillator modes for state/operator text output.
        pub const render_modes = [_]basis_generation.RenderAtom{
            .{ .id = kind(.eta), .name = "eta", .base_weight_ticks = 1, .show_label = false },
            .{ .id = kind(.xi), .name = "xi", .base_weight_ticks = 0, .show_label = false },
        };
        /// render_seed_bits names the finite xi zero-mode seed factor.
        pub const render_seed_bits = [_]basis_generation.RenderAtom{
            .{ .id = 0, .name = "xi", .base_weight_ticks = 0, .fixed_weight_ticks = 0, .show_label = false },
        };
        /// render_table maps compact eta-xi ids to local ghost fields.
        pub const render_table = basis_generation.RenderTable{ .modes = &render_modes, .seed_bits = &render_seed_bits };

        /// modeCapacity returns the finite oscillator-band capacity for a level budget.
        pub fn modeCapacity(comptime max_level_ticks: u32) usize {
            return etaXiModeCapacity(max_level_ticks);
        }

        /// seedCapacity returns the number of finite xi zero-mode seeds.
        pub fn seedCapacity() usize {
            return 2;
        }

        /// writeSeeds writes finite xi zero-mode seed subsets into a product vector.
        pub fn writeSeeds(quantum_offset: usize, comptime total_quantum_count: usize, seeds: []basis_generation.Seed, quantum_storage: []i32) ![]const basis_generation.Seed {
            const seed_families = [_]basis_generation.SeedFamily{basis_generation.Preset.etaXiSeedFamily(kind(.xi), 0)};
            var seed_options_storage: [1]basis_generation.SeedOption = undefined;
            const seed_options = try basis_generation.buildSeedOptions(&seed_families, &seed_options_storage);
            var local_seeds_storage: [2]basis_generation.Seed = undefined;
            var local_quantum_storage: [2]i32 = undefined;
            const local_seeds = try basis_generation.buildFermionicSeedSubsets(seed_options, quantum_schema.len, &local_seeds_storage, &local_quantum_storage);
            if (seeds.len < local_seeds.len or quantum_storage.len < local_seeds.len * total_quantum_count) return error.ContextTooSmall;
            for (local_seeds, 0..) |seed, index| {
                seeds[index] = try basis_generation.copySeed(seed, quantum_offset, total_quantum_count, quantum_storage[index * total_quantum_count .. (index + 1) * total_quantum_count]);
            }
            return seeds[0..local_seeds.len];
        }

        /// writeModes writes component-tagged positive eta-xi bands.
        pub fn writeModes(comptime max_level_ticks: u32, comptime component: u16, quantum_offset: usize, comptime total_quantum_count: usize, modes: []basis_generation.Mode, quantum_storage: []i32) ![]const basis_generation.Mode {
            const families = basis_generation.Preset.etaXiOscillatorFamilies(kind(.eta), kind(.xi), component);
            const written = try basis_generation.buildOscillatorModes(&families, max_level_ticks, modes);
            if (quantum_storage.len < written.len * total_quantum_count) return error.ContextTooSmall;
            for (written, 0..) |*mode, index| {
                mode.quantum_delta = try basis_generation.copyQuantumDelta(mode.quantum_delta, quantum_offset, total_quantum_count, quantum_storage[index * total_quantum_count .. (index + 1) * total_quantum_count]);
            }
            return written;
        }

        /// stream enumerates compact eta-xi words with the xi zero-mode seed.
        pub fn stream(comptime max_level_ticks: u32, comptime max_depth: usize, query: basis_generation.Query, sink: anytype) !void {
            var seeds_storage: [2]basis_generation.Seed = undefined;
            var seed_quantum_storage: [2]i32 = undefined;
            const seeds = try writeSeeds(0, quantum_schema.len, &seeds_storage, &seed_quantum_storage);

            var modes_storage: [etaXiModeCapacity(max_level_ticks)]basis_generation.Mode = undefined;
            var mode_quantum_storage: [modes_storage.len * quantum_schema.len]i32 = undefined;
            const modes = try writeModes(max_level_ticks, 0, 0, quantum_schema.len, &modes_storage, &mode_quantum_storage);
            var storage = basis_generation.StackContext(modes_storage.len, max_level_ticks, quantum_schema.len, max_depth){};
            var context = storage.context();
            return basis_generation.stream(.{
                .quantum_schema = quantum_schema,
                .modes = modes,
                .seeds = seeds,
            }, query, &context, sink);
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
    const holomorphic = Spec.ZeroModeRule{ .sector = zeroSector(.sphere), .expr = .{ .constant_fermion = .{
        .support = .sphere_holomorphic,
        .fermion_kind_ids = &.{kind(.xi)},
        .normalization = .one,
    } } };
    if (!cfg.include_antiholomorphic_copy) return [_]Spec.ZeroModeRule{holomorphic};
    return [_]Spec.ZeroModeRule{
        holomorphic,
        .{ .sector = zeroSector(.sphere), .expr = .{ .constant_fermion = .{
            .support = .sphere_antiholomorphic,
            .fermion_kind_ids = &.{kind(.xit)},
            .normalization = .one,
        } } },
    };
}

fn sphereZeroStorage(comptime cfg: EtaXiSphereConfig) if (cfg.include_antiholomorphic_copy) [2]zero_mode.Rule else [1]zero_mode.Rule {
    const spec = sphereZeroSpec(cfg);
    return Spec.zeroModeRules(&spec);
}

fn torusZeroSpec(comptime cfg: EtaXiSphereConfig) if (cfg.include_antiholomorphic_copy) [2]Spec.ZeroModeRule else [1]Spec.ZeroModeRule {
    const holomorphic = Spec.ZeroModeRule{ .sector = zeroSector(.torus), .expr = .{ .constant_fermion = .{
        .support = .torus_holomorphic,
        .fermion_kind_ids = &.{kind(.xi)},
        .normalization = .one,
    } } };
    if (!cfg.include_antiholomorphic_copy) return [_]Spec.ZeroModeRule{holomorphic};
    return [_]Spec.ZeroModeRule{
        holomorphic,
        .{ .sector = zeroSector(.torus), .expr = .{ .constant_fermion = .{
            .support = .torus_antiholomorphic,
            .fermion_kind_ids = &.{kind(.xit)},
            .normalization = .one,
        } } },
    };
}

fn torusZeroStorage(comptime cfg: EtaXiSphereConfig) if (cfg.include_antiholomorphic_copy) [2]zero_mode.Rule else [1]zero_mode.Rule {
    const spec = torusZeroSpec(cfg);
    return Spec.zeroModeRules(&spec);
}
const sphere_holomorphic_operator_spec = [_]Spec.Operator{
    .{ .name = "eta", .kind = kind(.eta), .support = .holomorphic, .insertion = .single, .statistics = .fermionic, .infinity = .{ .primary = .{ .holomorphic_power = -2 } } },
    .{ .name = "xi", .kind = kind(.xi), .support = .holomorphic, .insertion = .single, .statistics = .fermionic, .zero_mode_consumable = true, .infinity = .{ .primary = .{} } },
};

const sphere_full_operator_spec = sphere_holomorphic_operator_spec ++ [_]Spec.Operator{
    .{ .name = "etat", .kind = kind(.etat), .support = .antiholomorphic, .insertion = .single, .statistics = .fermionic, .infinity = .{ .primary = .{ .antiholomorphic_power = -2 } } },
    .{ .name = "xit", .kind = kind(.xit), .support = .antiholomorphic, .insertion = .single, .statistics = .fermionic, .zero_mode_consumable = true, .infinity = .{ .primary = .{} } },
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
const sphere_holomorphic_infinity_storage = Spec.infinityData(&sphere_holomorphic_operator_spec);
const sphere_full_infinity_storage = Spec.infinityData(&sphere_full_operator_spec);

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
    const selected_infinity = if (include_antiholomorphic_copy) sphere_full_infinity_storage else sphere_holomorphic_infinity_storage;
    return struct {
        const sphere_wick: []const wick.Rule = &selected_wick;
        const torus_wick: []const wick.Rule = &selected_torus_wick;
        const sphere_fermion_kinds: []const operators.OperatorKindId = &selected_fermions;
        const sphere_infinity_data = &selected_infinity;
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
            .infinity_data = rules.sphere_infinity_data,
        }){};

        /// torus selects eta-xi torus prime-form log-derivative Wick and xi zero-mode rules.
        pub const torus = declare.correlatorConfig(.{
            .wick_rules = rules.torus_wick,
            .zero_modes = &torus_zero_storage,
            .fermion_kinds = rules.sphere_fermion_kinds,
            .infinity_data = rules.sphere_infinity_data,
        }){};
    };
}
