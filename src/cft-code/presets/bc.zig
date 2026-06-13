const std = @import("std");
const basis_generation = @import("../basis-generation/basis-generation.zig");
const generated_fixtures = @import("../correlators/generated_fixtures.zig");
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
    torus,
};

fn kind(comptime family: Family) operators.OperatorKindId {
    return declare.familyKind(namespace, family);
}

fn zeroSector(comptime sector: ZeroSector) zero_mode.Sector {
    return declare.sectorId(namespace, sector);
}

const BcSphereConfig = struct {
    include_antiholomorphic_copy: bool = true,
    quantum_schema: []const basis_generation.Quantum = &basis_generation.Preset.ghost_schema,
};

/// bcSphere builds the generated preset type for the sphere bc ghost CFT.
pub fn bcSphere(comptime cfg: BcSphereConfig) type {
    return if (cfg.include_antiholomorphic_copy) GeneratedBcSphereFull else GeneratedBcSphere;
}

const GeneratedBcSphereFull = struct {
    const Base = generated_fixtures.BcSphereFull;

    /// op exposes descriptor-generated bc ghost local operator builders.
    pub const op = struct {
        /// b builds a holomorphic b-ghost insertion.
        pub fn b(builder: anytype, n: u8, z: Handle.Coord) !Operator {
            return Base.field("b").localSingle(builder, z, n, .{});
        }

        /// c builds a holomorphic c-ghost insertion.
        pub fn c(builder: anytype, n: u8, z: Handle.Coord) !Operator {
            return Base.field("c").localSingle(builder, z, n, .{});
        }

        /// bt builds an antiholomorphic b-ghost insertion.
        pub fn bt(builder: anytype, n: u8, zbar: Handle.Coord) !Operator {
            return Base.field("bt").localSingle(builder, zbar, n, .{});
        }

        /// ct builds an antiholomorphic c-ghost insertion.
        pub fn ct(builder: anytype, n: u8, zbar: Handle.Coord) !Operator {
            return Base.field("ct").localSingle(builder, zbar, n, .{});
        }
    };
    /// config exposes descriptor-generated correlator configs for this preset.
    pub const config = Base.config;
    /// basis streams descriptor-generated compact bc ghost mode words.
    pub const basis = Base.basis;
    /// text exposes bounded result-inspection sinks.
    pub const text = Base.text;

    /// local constructs a label-preserving local-operator builder.
    pub fn local(allocator: std.mem.Allocator) !Builder {
        return shared.Local.init(allocator);
    }

    /// correlator streams descriptor-generated rule matches for bc insertions.
    pub fn correlator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
        return shared.streamCorrelator(config_ptr, ops, sink);
    }
};

const GeneratedBcSphere = struct {
    const Base = generated_fixtures.Bc;

    /// op exposes descriptor-generated bc ghost local operator builders.
    pub const op = struct {
        /// b builds a holomorphic b-ghost insertion.
        pub fn b(builder: anytype, n: u8, z: Handle.Coord) !Operator {
            return Base.field("b").localSingle(builder, z, n, .{});
        }

        /// c builds a holomorphic c-ghost insertion.
        pub fn c(builder: anytype, n: u8, z: Handle.Coord) !Operator {
            return Base.field("c").localSingle(builder, z, n, .{});
        }
    };
    /// config exposes descriptor-generated correlator configs for this preset.
    pub const config = Base.config;
    /// basis streams descriptor-generated compact bc ghost mode words.
    pub const basis = Base.basis;
    /// text exposes bounded result-inspection sinks.
    pub const text = Base.text;

    /// local constructs a label-preserving local-operator builder.
    pub fn local(allocator: std.mem.Allocator) !Builder {
        return shared.Local.init(allocator);
    }

    /// correlator streams descriptor-generated rule matches for bc insertions.
    pub fn correlator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
        return shared.streamCorrelator(config_ptr, ops, sink);
    }
};

fn bcModeCapacity(comptime max_level_ticks: u32) usize {
    if (max_level_ticks == 0) return 0;
    return max_level_ticks + if (max_level_ticks >= 2) max_level_ticks - 1 else 0;
}

fn BcBasis(comptime cfg: BcSphereConfig) type {
    return struct {
        /// quantum_schema carries the one-slot ghost-number filter.
        pub const quantum_schema = cfg.quantum_schema;
        /// render_modes names compact oscillator modes for state/operator text output.
        pub const render_modes = [_]basis_generation.RenderAtom{
            .{ .id = kind(.b), .name = "b", .base_weight_ticks = 2, .show_label = false },
            .{ .id = kind(.c), .name = "c", .base_weight_ticks = -1, .show_label = false },
        };
        /// render_seed_bits names finite c-ghost seed factors.
        pub const render_seed_bits = [_]basis_generation.RenderAtom{
            .{ .id = 0, .name = "c", .base_weight_ticks = -1, .fixed_weight_ticks = -1, .show_label = false },
            .{ .id = 1, .name = "c", .base_weight_ticks = -1, .fixed_weight_ticks = 0, .show_label = false },
        };
        /// render_table maps compact bc ids to local ghost fields.
        pub const render_table = basis_generation.RenderTable{ .modes = &render_modes, .seed_bits = &render_seed_bits };

        /// modeCapacity returns the finite oscillator-band capacity for a level budget.
        pub fn modeCapacity(comptime max_level_ticks: u32) usize {
            return bcModeCapacity(max_level_ticks);
        }

        /// seedCapacity returns the number of finite ghost primary seeds.
        pub fn seedCapacity() usize {
            return 3;
        }

        /// writeSeeds writes finite c-seed subsets into a product quantum vector.
        pub fn writeSeeds(quantum_offset: usize, comptime total_quantum_count: usize, seeds: []basis_generation.Seed, quantum_storage: []i32) ![]const basis_generation.Seed {
            const seed_families = [_]basis_generation.SeedFamily{basis_generation.Preset.bcSeedFamily(kind(.c), 0)};
            var seed_options_storage: [2]basis_generation.SeedOption = undefined;
            const seed_options = try basis_generation.buildSeedOptions(&seed_families, &seed_options_storage);
            var local_seeds_storage: [4]basis_generation.Seed = undefined;
            var local_quantum_storage: [4]i32 = undefined;
            const local_seeds = try basis_generation.buildFermionicSeedSubsets(seed_options, quantum_schema.len, &local_seeds_storage, &local_quantum_storage);
            const seed_count = local_seeds.len - 1;
            if (seeds.len < seed_count or quantum_storage.len < seed_count * total_quantum_count) return error.ContextTooSmall;
            for (local_seeds[1..], 0..) |seed, index| {
                seeds[index] = try basis_generation.copySeed(seed, quantum_offset, total_quantum_count, quantum_storage[index * total_quantum_count .. (index + 1) * total_quantum_count]);
            }
            return seeds[0..seed_count];
        }

        /// writeModes writes component-tagged positive bc ghost bands.
        pub fn writeModes(comptime max_level_ticks: u32, comptime component: u16, quantum_offset: usize, comptime total_quantum_count: usize, modes: []basis_generation.Mode, quantum_storage: []i32) ![]const basis_generation.Mode {
            const families = basis_generation.Preset.bcOscillatorFamilies(kind(.b), kind(.c), component);
            const written = try basis_generation.buildOscillatorModes(&families, max_level_ticks, modes);
            if (quantum_storage.len < written.len * total_quantum_count) return error.ContextTooSmall;
            for (written, 0..) |*mode, index| {
                mode.quantum_delta = try basis_generation.copyQuantumDelta(mode.quantum_delta, quantum_offset, total_quantum_count, quantum_storage[index * total_quantum_count .. (index + 1) * total_quantum_count]);
            }
            return written;
        }

        /// stream enumerates compact bc ghost words with finite c-seed choices.
        pub fn stream(comptime max_level_ticks: u32, comptime max_depth: usize, query: basis_generation.Query, sink: anytype) !void {
            var seeds_storage: [seedCapacity()]basis_generation.Seed = undefined;
            var seed_quantum_storage: [seedCapacity() * quantum_schema.len]i32 = undefined;
            const seeds = try writeSeeds(0, quantum_schema.len, &seeds_storage, &seed_quantum_storage);

            var modes_storage: [bcModeCapacity(max_level_ticks)]basis_generation.Mode = undefined;
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
fn BcSphereOp(comptime include_antiholomorphic_copy: bool) type {
    const Holomorphic = struct {
        /// b builds a holomorphic b-ghost insertion.
        pub fn b(local: anytype, n: u8, z: Handle.Coord) !Operator {
            return declare.operatorBuilder(bcOperator(.b)).single(local, z, n, .{});
        }

        /// c builds a holomorphic c-ghost insertion.
        pub fn c(local: anytype, n: u8, z: Handle.Coord) !Operator {
            return declare.operatorBuilder(bcOperator(.c)).single(local, z, n, .{});
        }
    };

    if (!include_antiholomorphic_copy) return Holomorphic;

    return struct {
        /// b builds a holomorphic b-ghost insertion.
        pub const b = Holomorphic.b;
        /// c builds a holomorphic c-ghost insertion.
        pub const c = Holomorphic.c;

        /// bt builds an antiholomorphic b-ghost insertion.
        pub fn bt(local: anytype, n: u8, zbar: Handle.Coord) !Operator {
            return declare.operatorBuilder(bcOperator(.bt)).single(local, zbar, n, .{});
        }

        /// ct builds an antiholomorphic c-ghost insertion.
        pub fn ct(local: anytype, n: u8, zbar: Handle.Coord) !Operator {
            return declare.operatorBuilder(bcOperator(.ct)).single(local, zbar, n, .{});
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

fn sphereZeroSpec(comptime cfg: BcSphereConfig) if (cfg.include_antiholomorphic_copy) [2]Spec.ZeroModeRule else [1]Spec.ZeroModeRule {
    const holomorphic = Spec.ZeroModeRule{ .sector = zeroSector(.sphere), .expr = .{ .top_form_fermion = .{
        .support = .sphere_holomorphic,
        .field_kind_ids = &.{kind(.c)},
        .normalization = .one,
    } } };
    if (!cfg.include_antiholomorphic_copy) return [_]Spec.ZeroModeRule{holomorphic};
    return [_]Spec.ZeroModeRule{
        holomorphic,
        .{ .sector = zeroSector(.sphere), .expr = .{ .top_form_fermion = .{
            .support = .sphere_antiholomorphic,
            .field_kind_ids = &.{kind(.ct)},
            .normalization = .one,
        } } },
    };
}

fn sphereZeroStorage(comptime cfg: BcSphereConfig) if (cfg.include_antiholomorphic_copy) [2]zero_mode.Rule else [1]zero_mode.Rule {
    const spec = sphereZeroSpec(cfg);
    return Spec.zeroModeRules(&spec);
}

const sphere_holomorphic_operator_spec = [_]Spec.Operator{
    .{ .name = "b", .kind = kind(.b), .support = .holomorphic, .insertion = .single, .statistics = .fermionic, .infinity = .{ .primary = .{ .holomorphic_power = -4 } } },
    .{ .name = "c", .kind = kind(.c), .support = .holomorphic, .insertion = .single, .statistics = .fermionic, .zero_mode_consumable = true, .infinity = .{ .primary = .{ .holomorphic_power = 2 } } },
};

const sphere_full_operator_spec = sphere_holomorphic_operator_spec ++ [_]Spec.Operator{
    .{ .name = "bt", .kind = kind(.bt), .support = .antiholomorphic, .insertion = .single, .statistics = .fermionic, .infinity = .{ .primary = .{ .antiholomorphic_power = -4 } } },
    .{ .name = "ct", .kind = kind(.ct), .support = .antiholomorphic, .insertion = .single, .statistics = .fermionic, .zero_mode_consumable = true, .infinity = .{ .primary = .{ .antiholomorphic_power = 2 } } },
};

const sphere_holomorphic_fermion_storage = Spec.fermionKinds(&sphere_holomorphic_operator_spec);

const sphere_full_fermion_storage = Spec.fermionKinds(&sphere_full_operator_spec);
const sphere_holomorphic_infinity_storage = Spec.infinityData(&sphere_holomorphic_operator_spec);
const sphere_full_infinity_storage = Spec.infinityData(&sphere_full_operator_spec);

const sphere_holomorphic_wick_spec = [_]Spec.WickRule{
    .{ .left = kind(.b), .right = kind(.c), .expr = bcBC() },
};

const sphere_full_wick_spec = sphere_holomorphic_wick_spec ++ [_]Spec.WickRule{
    .{ .left = kind(.bt), .right = kind(.ct), .expr = bcBtCt() },
};

const sphere_holomorphic_wick_storage = Spec.wickRules(&sphere_holomorphic_wick_spec, &sphere_holomorphic_operator_spec);

const sphere_full_wick_storage = Spec.wickRules(&sphere_full_wick_spec, &sphere_full_operator_spec);

const torus_wick_spec = [_]Spec.WickRule{
    .{ .left = kind(.b), .right = kind(.c), .coordinate_kernels = &.{.elliptic_prime_form} },
    .{ .left = kind(.bt), .right = kind(.ct), .coordinate_kernels = &.{.elliptic_prime_form} },
};

const sphere_holomorphic_zero_spec = sphereZeroSpec(.{ .include_antiholomorphic_copy = false });

const sphere_full_zero_spec = sphereZeroSpec(.{});
const torus_zero_spec = [_]Spec.ZeroModeRule{
    .{
        .sector = zeroSector(.torus),
        .kind = .torus_bc_moduli,
        .consumes = &.{ kind(.b), kind(.c), kind(.bt), kind(.ct) },
    },
};

fn bcSphereSpec(comptime include_antiholomorphic_copy: bool) Spec.Theory {
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
    .wick_rules = &torus_wick_spec,
    .zero_modes = &torus_zero_spec,
};

const disk_boundary_operator_spec = [_]Spec.Operator{
    .{ .name = "bBoundary", .kind = kind(.b_boundary), .support = .boundary, .insertion = .single, .statistics = .fermionic },
    .{ .name = "cBoundary", .kind = kind(.c_boundary), .support = .boundary, .insertion = .single, .statistics = .fermionic, .zero_mode_consumable = true },
};

const disk_full_operator_spec = sphere_full_operator_spec ++ disk_boundary_operator_spec;

fn bcOperator(comptime family: Family) Spec.Operator {
    const kind_id = kind(family);
    inline for (sphere_full_operator_spec) |operator| {
        if (operator.kind == kind_id) return operator;
    }
    @compileError("missing bc operator spec");
}

fn bcBoundaryOperator(comptime family: Family) Spec.Operator {
    const kind_id = kind(family);
    inline for (disk_boundary_operator_spec) |operator| {
        if (operator.kind == kind_id) return operator;
    }
    @compileError("missing bc boundary operator spec");
}

fn assertSphereSpec(comptime include_antiholomorphic_copy: bool, comptime wick_count: usize, comptime zero_count: usize, comptime fermion_count: usize) void {
    const spec = bcSphereSpec(include_antiholomorphic_copy);
    if (spec.wick_rules.len != wick_count) @compileError("bc sphere spec Wick count does not match lowered rules");
    if (spec.zero_modes.len != zero_count) @compileError("bc sphere spec zero-mode count does not match lowered rules");
    if (spec.operators.len != fermion_count) @compileError("bc sphere spec fermion coverage does not match lowered rules");
}

fn assertTorusDraftSpec() void {
    if (torus_draft_spec.surface.kind != .torus) @compileError("bc torus draft spec surface kind is incomplete");
    if (torus_draft_spec.surface.coordinate_model != .elliptic) @compileError("bc torus draft spec coordinate model is incomplete");
    if (torus_draft_spec.surface.modular_parameters.len != 1) @compileError("bc torus draft spec modular metadata is incomplete");
    if (torus_draft_spec.surface.source != .stringbook) @compileError("bc torus draft spec source convention is incomplete");
    if (torus_draft_spec.operators.len != sphere_full_operator_spec.len) @compileError("bc torus draft spec operator metadata is incomplete");
    if (torus_draft_spec.wick_rules.len != sphere_full_wick_spec.len) @compileError("bc torus draft spec Wick metadata is incomplete");
    if (Spec.wickCoordinateKernelCount(torus_draft_spec.wick_rules, .elliptic_prime_form) != 2) @compileError("bc torus draft spec prime-form metadata is incomplete");
    if (Spec.wickCoordinateKernelCount(torus_draft_spec.wick_rules, .rational_pole) != 0) @compileError("bc torus draft spec still uses rational pole metadata");
    if (torus_draft_spec.zero_modes.len != 1) @compileError("bc torus draft spec zero-mode metadata is incomplete");
    if (Spec.zeroModeConsumeKindCount(torus_draft_spec.zero_modes[0]) != 4) @compileError("bc torus draft spec zero-mode coverage is incomplete");
}

fn BcSphereRules(comptime include_antiholomorphic_copy: bool) type {
    const selected_wick = if (include_antiholomorphic_copy) sphere_full_wick_storage else sphere_holomorphic_wick_storage;
    const selected_fermions = if (include_antiholomorphic_copy) sphere_full_fermion_storage else sphere_holomorphic_fermion_storage;
    const selected_infinity = if (include_antiholomorphic_copy) sphere_full_infinity_storage else sphere_holomorphic_infinity_storage;
    return struct {
        const sphere_wick: []const wick.Rule = &selected_wick;
        const sphere_fermion_kinds: []const operators.OperatorKindId = &selected_fermions;
        const sphere_infinity_data = &selected_infinity;
    };
}

fn BcSphereCorrelatorConfig(comptime cfg: BcSphereConfig) type {
    const rules = BcSphereRules(cfg.include_antiholomorphic_copy);
    return struct {
        const sphere_zero_storage = sphereZeroStorage(cfg);
        comptime {
            assertSphereSpec(cfg.include_antiholomorphic_copy, rules.sphere_wick.len, sphere_zero_storage.len, rules.sphere_fermion_kinds.len);
            assertTorusDraftSpec();
        }

        /// sphere selects bc sphere Wick and zero-mode rules.
        pub const sphere = declare.correlatorConfig(.{
            .wick_rules = rules.sphere_wick,
            .zero_modes = &sphere_zero_storage,
            .fermion_kinds = rules.sphere_fermion_kinds,
            .infinity_data = rules.sphere_infinity_data,
        }){};
    };
}
const BcDiskConfig = struct {
    include_mixed_bulk_boundary: bool = true,
};

const BcDiskBoundaryOp = struct {
    /// bBoundary builds a boundary b-ghost insertion.
    pub fn bBoundary(local: anytype, n: u8, y: Handle.BoundaryCoord) !Operator {
        return declare.operatorBuilder(bcBoundaryOperator(.b_boundary)).boundarySingle(local, y, n, .{});
    }

    /// cBoundary builds a boundary c-ghost insertion.
    pub fn cBoundary(local: anytype, n: u8, y: Handle.BoundaryCoord) !Operator {
        return declare.operatorBuilder(bcBoundaryOperator(.c_boundary)).boundarySingle(local, y, n, .{});
    }
};

fn BcBoundaryExtension(comptime cfg: BcDiskConfig) type {
    const data = BcDiskData(cfg);
    return declare.BoundaryExtension(.{
        .op = BcDiskBoundaryOp,
        .wick_rules = if (cfg.include_mixed_bulk_boundary) &disk_full_wick_storage else &disk_boundary_wick_storage,
        .zero_modes = data.disk_zero_modes,
        .fermion_kinds = data.disk_fermion_kinds,
    });
}

/// boundaryExtension declares boundary and mixed bulk-boundary bc rules on the disk.
pub fn boundaryExtension(comptime cfg: BcDiskConfig) BcBoundaryExtension(cfg) {
    return .{};
}

const disk_boundary_wick_spec = [_]Spec.WickRule{
    .{ .left = kind(.b_boundary), .right = kind(.c_boundary), .expr = bcBC() },
};

const disk_full_wick_spec = disk_boundary_wick_spec ++ [_]Spec.WickRule{
    .{ .left = kind(.b), .right = kind(.c_boundary), .expr = bcBC() },
    .{ .left = kind(.c), .right = kind(.b_boundary), .expr = bcBC() },
    .{ .left = kind(.bt), .right = kind(.c_boundary), .expr = bcBtCt() },
    .{ .left = kind(.ct), .right = kind(.b_boundary), .expr = bcBtCt() },
};

const disk_boundary_wick_storage = Spec.wickRules(&disk_boundary_wick_spec, &disk_boundary_operator_spec);

const disk_full_wick_storage = Spec.wickRules(&disk_full_wick_spec, &disk_full_operator_spec);

const disk_boundary_fermion_storage = Spec.fermionKinds(&disk_boundary_operator_spec);

const disk_full_fermion_storage = Spec.fermionKinds(&disk_full_operator_spec);

fn diskZeroSpec() [1]Spec.ZeroModeRule {
    return [_]Spec.ZeroModeRule{
        .{ .sector = zeroSector(.disk), .expr = .{ .top_form_fermion = .{
            .support = .disk_doubled,
            .field_kind_ids = &.{ kind(.c), kind(.ct), kind(.c_boundary) },
            .normalization = .one,
        } } },
    };
}

fn diskZeroStorage(comptime cfg: BcDiskConfig) [1]zero_mode.Rule {
    _ = cfg;
    const spec = diskZeroSpec();
    return Spec.zeroModeRules(&spec);
}

fn BcDiskData(comptime cfg: BcDiskConfig) type {
    const selected_fermions = if (cfg.include_mixed_bulk_boundary) disk_full_fermion_storage else disk_boundary_fermion_storage;
    return struct {
        const disk_zero_storage = diskZeroStorage(cfg);

        const disk_zero_modes: []const zero_mode.Rule = &disk_zero_storage;
        const disk_fermion_kinds: []const operators.OperatorKindId = &selected_fermions;
    };
}

test "bc schema builders return opaque local tokens" {
    const testing = std.testing;
    const Ghost = bcSphere(.{ .include_antiholomorphic_copy = false });

    var local = try Ghost.local(testing.allocator);
    defer local.deinit();

    const z1 = try local.coord("z1");
    const z2 = try local.coord("z2");
    const b = try Ghost.op.b(&local, 1, z1);
    const c = try Ghost.op.c(&local, 2, z2);
    const ops = try local.ops(.{ b, c });

    try testing.expect(@typeInfo(@typeInfo(@TypeOf(b)).pointer.child) == .@"opaque");
    try testing.expect(@typeInfo(@typeInfo(@TypeOf(c)).pointer.child) == .@"opaque");
    try testing.expect(@typeInfo(@typeInfo(@TypeOf(ops)).pointer.child) == .@"opaque");
}

test "bc boundary schema builders return opaque local tokens" {
    const testing = std.testing;

    var local = try Local.init(testing.allocator);
    defer local.deinit();

    const y = try local.boundaryCoord("y");
    const b = try BcDiskBoundaryOp.bBoundary(&local, 1, y);
    const c = try BcDiskBoundaryOp.cBoundary(&local, 2, y);
    const ops = try local.ops(.{ b, c });

    try testing.expect(@typeInfo(@typeInfo(@TypeOf(b)).pointer.child) == .@"opaque");
    try testing.expect(@typeInfo(@typeInfo(@TypeOf(c)).pointer.child) == .@"opaque");
    try testing.expect(@typeInfo(@typeInfo(@TypeOf(ops)).pointer.child) == .@"opaque");
}
