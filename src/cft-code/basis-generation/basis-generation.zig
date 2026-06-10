const std = @import("std");

/// Error reports invalid compact descriptors or insufficient caller scratch.
pub const Error = error{
    ContextTooSmall,
    InvalidDescriptor,
    InvalidQuery,
    UnknownQuantum,
    UnsupportedQuantumFilter,
    WordStackTooSmall,
};

/// Statistics controls local repetition of one finite mode alternative.
pub const Statistics = enum {
    bosonic,
    fermionic,
};

/// QuantumKind selects the fast suffix-reachability rule for one charge slot.
pub const QuantumKind = enum {
    additive,
    zn,
    tensor_rep,
};

/// Quantum describes one compact quantum-number slot in a presentation.
pub const Quantum = struct {
    name: []const u8 = "",
    kind: QuantumKind,
    modulus: u8 = 0,
    representation_space: u32 = 0,
};

/// Mode is one precompiled creation-mode alternative in canonical order.
pub const Mode = struct {
    id: u32,
    component: u16 = 0,
    label: u16 = 0,
    weight_ticks: u32,
    base_weight_ticks: i32 = 0,
    derivative_step_ticks: u32 = 1,
    statistics: Statistics,
    quantum_delta: []const i32 = &.{},
    body: u32 = 0,
};

/// OscillatorFamily lowers a primitive free-field mode family to finite bands.
pub const OscillatorFamily = struct {
    id: u32,
    component: u16 = 0,
    statistics: Statistics,
    first_tick: u32,
    step_tick: u32,
    base_weight_ticks: i32 = 0,
    derivative_step_ticks: u32 = 1,
    multiplicity: u16 = 1,
    quantum_delta: []const i32 = &.{},
    body: u32 = 0,
};

/// SeedBodyKind says how Seed.body should be interpreted.
pub const SeedBodyKind = enum {
    none,
    finite_mask,
    primary,
};

/// Seed is one primary state from which descendants are generated.
pub const Seed = struct {
    id: u16 = 0,
    weight_ticks: i32 = 0,
    component_weight_ticks: []const i32 = &.{},
    quantum_values: []const i32 = &.{},
    body_kind: SeedBodyKind = .none,
    body: u32 = 0,
};

/// PrimarySeed describes one charged highest-weight seed.
pub const PrimarySeed = struct {
    id: u16,
    weight_ticks: i32 = 0,
    component_weight_ticks: []const i32 = &.{},
    quantum_values: []const i32 = &.{},
};

/// primarySeed builds a seed represented by one primary atom.
pub fn primarySeed(seed: PrimarySeed) Seed {
    return .{
        .id = seed.id,
        .weight_ticks = seed.weight_ticks,
        .component_weight_ticks = seed.component_weight_ticks,
        .quantum_values = seed.quantum_values,
        .body_kind = .primary,
    };
}

/// SeedOption is one finite nonpositive-weight primitive allowed in a seed.
pub const SeedOption = struct {
    id: u32,
    component: u16 = 0,
    label: u16 = 0,
    weight_ticks: i32,
    statistics: Statistics = .fermionic,
    quantum_delta: []const i32 = &.{},
    body: u32 = 0,
};

/// SeedFamily lowers finite nonpositive local primitives to seed options.
pub const SeedFamily = struct {
    id: u32,
    component: u16 = 0,
    first_weight_ticks: i32,
    step_tick: u32,
    last_weight_ticks: i32 = 0,
    statistics: Statistics = .fermionic,
    multiplicity: u16 = 1,
    quantum_delta: []const i32 = &.{},
    body: u32 = 0,
};

/// Presentation is the immutable compact data consumed by the enumerator.
pub const Presentation = struct {
    id: u16 = 0,
    quantum_schema: []const Quantum = &.{},
    modes: []const Mode = &.{},
    seeds: []const Seed = &.{Seed{}},
};

/// WeightFilter selects exact-level or bounded-level streaming.
pub const WeightFilter = union(enum) {
    exact: i32,
    max: i32,
};

/// QuantumFilter constrains one named compact quantum slot.
pub const QuantumFilter = struct {
    slot: u8,
    value: i32,
};

/// quantumSlot returns the dense slot for a named quantum number.
pub fn quantumSlot(schema: []const Quantum, name: []const u8) !u8 {
    for (schema, 0..) |quantum, slot| {
        if (std.mem.eql(u8, quantum.name, name)) return @intCast(slot);
    }
    return Error.UnknownQuantum;
}

/// quantumFilter builds a dense slot filter from a named quantum number.
pub fn quantumFilter(schema: []const Quantum, name: []const u8, value: i32) !QuantumFilter {
    return .{ .slot = try quantumSlot(schema, name), .value = value };
}

/// LevelMatchFilter requires two product components to carry equal weights.
pub const LevelMatchFilter = struct {
    left_component: u16 = 0,
    right_component: u16 = 1,
};

/// Query is the small immutable record passed to the compact backend.
pub const Query = struct {
    weight: WeightFilter,
    quantum_filters: []const QuantumFilter = &.{},
    level_match: ?LevelMatchFilter = null,
    max_word_length: u16 = std.math.maxInt(u16),

    fn weightLimit(self: Query) i32 {
        return switch (self.weight) {
            .exact => |ticks| ticks,
            .max => |ticks| ticks,
        };
    }
};

/// ModeEntry is one borrowed word-stack item emitted to the sink.
pub const ModeEntry = struct {
    mode_index: u32,
    id: u32,
    component: u16,
    label: u16,
    weight_ticks: u32,
    base_weight_ticks: i32 = 0,
    derivative_step_ticks: u32 = 1,
    statistics: Statistics = .bosonic,
    body: u32,
};

/// Candidate is one streamed compact basis state.
pub const Candidate = struct {
    presentation: u16,
    seed: u16,
    seed_body: u32,
    base_weight_ticks: i32 = 0,
    base_component_weight_ticks: []const i32 = &.{},
    base_quantum_values: []const i32 = &.{},
    weight_ticks: i32,
    level_ticks: u32,
    component_weight_ticks: []const i32 = &.{},
    quantum_values: []const i32,
    modes: []const ModeEntry,

    /// structuralHash returns a stable non-rendered id for cache keys.
    pub fn structuralHash(self: Candidate) u64 {
        var hash: u64 = 14695981039346656037;
        hash = fnv(hash, self.presentation);
        hash = fnv(hash, self.seed);
        hash = fnv(hash, self.base_weight_ticks);
        hash = fnv(hash, self.weight_ticks);
        hash = fnv(hash, self.level_ticks);
        for (self.base_quantum_values) |value| hash = fnv(hash, value);
        for (self.modes) |mode| {
            hash = fnv(hash, mode.mode_index);
            hash = fnv(hash, mode.id);
            hash = fnv(hash, mode.component);
            hash = fnv(hash, mode.label);
            hash = fnv(hash, mode.weight_ticks);
        }
        return hash;
    }
};

/// OperatorAtom is one structural local factor for OPE and printing sinks.
pub const OperatorAtom = struct {
    field: u32,
    weight_ticks: i32 = 0,
    body: u32 = 0,
    component: u16 = 0,
    derivative: u16 = 0,
    label: u16 = 0,
    statistics: Statistics = .bosonic,
    source: Source = .descendant,

    /// Source separates seed factors from generated descendants.
    pub const Source = enum(u8) {
        seed,
        descendant,
    };
};

/// OperatorRecord borrows enough structural data to rebuild a state or operator.
pub const OperatorRecord = struct {
    presentation: u16,
    seed: u16,
    seed_body: u32 = 0,
    base_atoms: []const OperatorAtom = &.{},
    descendant_atoms: []const OperatorAtom = &.{},
    base_weight_ticks: i32 = 0,
    weight_ticks: i32,
    level_ticks: u32,
    base_quantum_values: []const i32 = &.{},
    quantum_values: []const i32 = &.{},
    base_component_weight_ticks: []const i32 = &.{},
    component_weight_ticks: []const i32 = &.{},
    structural_hash: u64 = 0,

    /// structuralHash returns a stable non-rendered id for operator records.
    pub fn structuralHash(self: OperatorRecord) u64 {
        if (self.structural_hash != 0) return self.structural_hash;
        var hash = operatorRecordHashPrefixFromValues(
            self.presentation,
            self.seed,
            self.seed_body,
            self.base_weight_ticks,
            self.weight_ticks,
            self.level_ticks,
            self.base_quantum_values,
            self.quantum_values,
        );
        for (self.base_atoms) |atom| hash = hashOperatorAtom(hash, atom);
        for (self.descendant_atoms) |atom| hash = hashOperatorAtom(hash, atom);
        return hash;
    }
};

/// RenderFormat selects how a streamed candidate is written for inspection.
pub const RenderFormat = enum {
    compact,
    state,
    operator_at_zero,
};

/// RenderOptions controls bounded basis text output.
pub const RenderOptions = struct {
    format: RenderFormat = .compact,
    insertion: []const u8 = "0",
    max_states: usize = std.math.maxInt(usize),
};

/// RenderAtom names one compact mode or seed atom for text lowering.
pub const RenderAtom = struct {
    id: u32,
    component: ?u16 = null,
    name: []const u8,
    base_weight_ticks: i32 = 0,
    derivative_step_ticks: u32 = 1,
    fixed_weight_ticks: ?i32 = null,
    show_label: bool = true,
};

/// RenderTable maps compact ids to display atoms without touching enumeration.
pub const RenderTable = struct {
    modes: []const RenderAtom = &.{},
    seed_bits: []const RenderAtom = &.{},

    /// modeAtom returns the display atom for a compact mode id and component.
    pub fn modeAtom(self: RenderTable, id: u32, component: u16) ?RenderAtom {
        var fallback: ?RenderAtom = null;
        for (self.modes) |atom| {
            if (atom.id != id) continue;
            if (atom.component) |expected| {
                if (expected == component) return atom;
            } else {
                fallback = atom;
            }
        }
        return fallback;
    }

    /// seedBitAtom returns the display atom for a finite seed-body bit.
    pub fn seedBitAtom(self: RenderTable, bit: usize) ?RenderAtom {
        for (self.seed_bits) |atom| {
            if (atom.id == bit) return atom;
        }
        return null;
    }
};

/// textSink returns a writer-backed sink for compact, state, or operator output.
pub fn textSink(writer: anytype, options: RenderOptions, table: RenderTable) TextSink(@TypeOf(writer)) {
    return .{ .writer = writer, .options = options, .table = table };
}

/// Context owns all mutable scratch needed by one streaming worker.
pub const Context = struct {
    word: []ModeEntry,
    component_weights: []i32 = &.{},
    quantum_values: []i32,
    add_min: []i32,
    add_max: []i32,
    finite_bits: []u64,

    /// reachabilitySlots returns the dense table length required per table.
    pub fn reachabilitySlots(mode_count: usize, max_ticks: u32, quantum_count: usize) usize {
        return (mode_count + 1) * (@as(usize, max_ticks) + 1) * quantum_count;
    }
};

/// OperatorContext owns bounded atom scratch for direct operator streaming.
pub const OperatorContext = struct {
    atoms: []OperatorAtom,
};

/// StackOperatorContext returns fixed-size atom scratch for operator records.
pub fn StackOperatorContext(comptime max_atoms: usize) type {
    return struct {
        atoms: [max_atoms]OperatorAtom = undefined,

        /// context borrows this stack storage as mutable operator scratch.
        pub fn context(self: *@This()) OperatorContext {
            return .{ .atoms = &self.atoms };
        }
    };
}

/// StackContext returns a fixed-size worker context for bounded basis calls.
pub fn StackContext(comptime mode_count: usize, comptime max_ticks: u32, comptime quantum_count: usize, comptime max_depth: usize) type {
    return StackContextWithComponents(mode_count, max_ticks, quantum_count, max_depth, 0);
}

/// StackContextWithComponents returns scratch with per-component weights.
pub fn StackContextWithComponents(comptime mode_count: usize, comptime max_ticks: u32, comptime quantum_count: usize, comptime max_depth: usize, comptime component_count: usize) type {
    return struct {
        word: [max_depth]ModeEntry = undefined,
        component_weights: [component_count]i32 = undefined,
        quantum_values: [quantum_count]i32 = undefined,
        add_min: [Context.reachabilitySlots(mode_count, max_ticks, quantum_count)]i32 = undefined,
        add_max: [Context.reachabilitySlots(mode_count, max_ticks, quantum_count)]i32 = undefined,
        finite_bits: [Context.reachabilitySlots(mode_count, max_ticks, quantum_count)]u64 = undefined,

        /// context borrows this stack storage as mutable enumeration scratch.
        pub fn context(self: *@This()) Context {
            return .{
                .word = &self.word,
                .component_weights = &self.component_weights,
                .quantum_values = &self.quantum_values,
                .add_min = &self.add_min,
                .add_max = &self.add_max,
                .finite_bits = &self.finite_bits,
            };
        }
    };
}

const quantum_plus = [_]i32{1};
const quantum_minus = [_]i32{-1};
const quantum_zero = [_]i32{0};

/// Preset builds compact families for the CFT sectors implemented first.
pub const Preset = struct {
    /// u1Charge returns one named additive integer U(1) quantum-number slot.
    pub fn u1Charge(comptime name: []const u8) Quantum {
        return .{ .name = name, .kind = .additive };
    }

    /// zn returns one named cyclic quantum-number slot.
    pub fn zn(comptime name: []const u8, comptime modulus: u8) Quantum {
        return .{ .name = name, .kind = .zn, .modulus = modulus };
    }

    /// tensorRepresentation returns a named tensor-code representation placeholder.
    pub fn tensorRepresentation(comptime name: []const u8, representation_space: u32) Quantum {
        return .{ .name = name, .kind = .tensor_rep, .representation_space = representation_space };
    }

    /// ghost_schema is the one-slot additive ghost-number U(1) schema.
    pub const ghost_schema = [_]Quantum{u1Charge("ghost-number")};
    /// eta_xi_schema is the one-slot additive eta-xi U(1) schema.
    pub const eta_xi_schema = [_]Quantum{u1Charge("eta-xi-number")};
    /// fermion_number_schema is the one-slot modulus-2 fermion-number schema.
    pub const fermion_number_schema = [_]Quantum{zn("fermion-number", 2)};

    /// freeBosonFamily describes integer-moded dX oscillators.
    pub fn freeBosonFamily(id: u32, component: u16, dimension: u16) OscillatorFamily {
        return .{
            .id = id,
            .component = component,
            .statistics = .bosonic,
            .first_tick = 1,
            .step_tick = 1,
            .multiplicity = dimension,
            .quantum_delta = &quantum_zero,
        };
    }

    /// nsFreeFermionFamily describes half-integer NS fermion modes in half-ticks.
    pub fn nsFreeFermionFamily(id: u32, component: u16, dimension: u16) OscillatorFamily {
        return .{
            .id = id,
            .component = component,
            .statistics = .fermionic,
            .first_tick = 1,
            .step_tick = 2,
            .base_weight_ticks = 1,
            .derivative_step_ticks = 2,
            .multiplicity = dimension,
            .quantum_delta = &quantum_plus,
        };
    }

    /// bcSeedFamily describes finite c and dc seed choices.
    pub fn bcSeedFamily(id: u32, component: u16) SeedFamily {
        return .{
            .id = id,
            .component = component,
            .first_weight_ticks = -1,
            .step_tick = 1,
            .last_weight_ticks = 0,
            .statistics = .fermionic,
            .quantum_delta = &quantum_plus,
        };
    }

    /// bcOscillatorFamilies describes positive b and c ghost jets.
    pub fn bcOscillatorFamilies(b_id: u32, c_id: u32, component: u16) [2]OscillatorFamily {
        return .{
            .{
                .id = b_id,
                .component = component,
                .statistics = .fermionic,
                .first_tick = 2,
                .step_tick = 1,
                .base_weight_ticks = 2,
                .quantum_delta = &quantum_minus,
            },
            .{
                .id = c_id,
                .component = component,
                .statistics = .fermionic,
                .first_tick = 1,
                .step_tick = 1,
                .base_weight_ticks = -1,
                .quantum_delta = &quantum_minus,
            },
        };
    }

    /// etaXiSeedFamily describes the xi zero-mode seed choice.
    pub fn etaXiSeedFamily(id: u32, component: u16) SeedFamily {
        return .{
            .id = id,
            .component = component,
            .first_weight_ticks = 0,
            .step_tick = 1,
            .last_weight_ticks = 0,
            .statistics = .fermionic,
            .quantum_delta = &quantum_minus,
        };
    }

    /// etaXiOscillatorFamilies describes positive eta and xi jets.
    pub fn etaXiOscillatorFamilies(eta_id: u32, xi_id: u32, component: u16) [2]OscillatorFamily {
        return .{
            .{
                .id = eta_id,
                .component = component,
                .statistics = .fermionic,
                .first_tick = 1,
                .step_tick = 1,
                .base_weight_ticks = 1,
                .quantum_delta = &quantum_plus,
            },
            .{
                .id = xi_id,
                .component = component,
                .statistics = .fermionic,
                .first_tick = 1,
                .step_tick = 1,
                .base_weight_ticks = 0,
                .quantum_delta = &quantum_minus,
            },
        };
    }
};

/// oscillatorModeCount returns the mode-band count needed for these families.
pub fn oscillatorModeCount(families: []const OscillatorFamily, max_ticks: u32) !usize {
    var count: usize = 0;
    for (families) |family| {
        if (family.first_tick == 0 or family.step_tick == 0 or family.multiplicity == 0) return Error.InvalidDescriptor;
        if (family.first_tick > max_ticks) continue;
        const level_count = ((max_ticks - family.first_tick) / family.step_tick) + 1;
        count += @as(usize, level_count) * family.multiplicity;
    }
    return count;
}

/// buildOscillatorModes writes finite mode bands into caller-owned storage.
pub fn buildOscillatorModes(families: []const OscillatorFamily, max_ticks: u32, out: []Mode) ![]Mode {
    const required = try oscillatorModeCount(families, max_ticks);
    if (out.len < required) return Error.ContextTooSmall;

    var written: usize = 0;
    for (families) |family| {
        if (family.first_tick == 0 or family.step_tick == 0 or family.multiplicity == 0) return Error.InvalidDescriptor;
        var tick = family.first_tick;
        while (tick <= max_ticks) : (tick += family.step_tick) {
            var label: u16 = 0;
            while (label < family.multiplicity) : (label += 1) {
                out[written] = .{
                    .id = family.id,
                    .component = family.component,
                    .label = label,
                    .weight_ticks = tick,
                    .base_weight_ticks = family.base_weight_ticks,
                    .derivative_step_ticks = family.derivative_step_ticks,
                    .statistics = family.statistics,
                    .quantum_delta = family.quantum_delta,
                    .body = family.body,
                };
                written += 1;
            }
        }
    }
    return out[0..written];
}

/// seedOptionCount returns the number of finite seed choices from families.
pub fn seedOptionCount(families: []const SeedFamily) !usize {
    var count: usize = 0;
    for (families) |family| {
        if (family.step_tick == 0 or family.multiplicity == 0 or family.first_weight_ticks > family.last_weight_ticks) return Error.InvalidDescriptor;
        const span: u32 = @intCast(family.last_weight_ticks - family.first_weight_ticks);
        const level_count = (span / family.step_tick) + 1;
        count += @as(usize, level_count) * family.multiplicity;
    }
    return count;
}

/// buildSeedOptions writes finite nonpositive seed options to caller storage.
pub fn buildSeedOptions(families: []const SeedFamily, out: []SeedOption) ![]SeedOption {
    const required = try seedOptionCount(families);
    if (out.len < required) return Error.ContextTooSmall;

    var written: usize = 0;
    for (families) |family| {
        if (family.step_tick == 0 or family.multiplicity == 0 or family.first_weight_ticks > family.last_weight_ticks) return Error.InvalidDescriptor;
        var weight = family.first_weight_ticks;
        while (weight <= family.last_weight_ticks) : (weight += @intCast(family.step_tick)) {
            var label: u16 = 0;
            while (label < family.multiplicity) : (label += 1) {
                out[written] = .{
                    .id = family.id,
                    .component = family.component,
                    .label = label,
                    .weight_ticks = weight,
                    .statistics = family.statistics,
                    .quantum_delta = family.quantum_delta,
                    .body = family.body,
                };
                written += 1;
            }
        }
    }
    return out[0..written];
}

/// fermionicSeedSubsetCount returns the number of seed subsets including empty.
pub fn fermionicSeedSubsetCount(options: []const SeedOption) !usize {
    if (options.len >= @bitSizeOf(usize)) return Error.ContextTooSmall;
    return @as(usize, 1) << @intCast(options.len);
}

/// buildFermionicSeedSubsets writes all canonical finite seed subsets.
pub fn buildFermionicSeedSubsets(options: []const SeedOption, quantum_count: usize, seeds: []Seed, quantum_storage: []i32) ![]const Seed {
    const required = try fermionicSeedSubsetCount(options);
    if (seeds.len < required or quantum_storage.len < required * quantum_count) return Error.ContextTooSmall;
    for (options) |option| {
        if (option.statistics != .fermionic) return Error.InvalidDescriptor;
    }

    var mask: usize = 0;
    while (mask < required) : (mask += 1) {
        const quantum = quantum_storage[mask * quantum_count .. (mask + 1) * quantum_count];
        @memset(quantum, 0);

        var weight: i32 = 0;
        var body: u32 = 0;
        for (options, 0..) |option, bit| {
            if ((mask & (@as(usize, 1) << @intCast(bit))) == 0) continue;
            weight += option.weight_ticks;
            body |= if (option.body != 0) option.body else @as(u32, 1) << @intCast(bit);
            for (0..quantum_count) |slot| {
                quantum[slot] += quantumDeltaFromSlice(option.quantum_delta, slot);
            }
        }

        seeds[mask] = .{
            .id = @intCast(mask),
            .weight_ticks = weight,
            .quantum_values = quantum,
            .body_kind = .finite_mask,
            .body = body,
        };
    }

    return seeds[0..required];
}

/// copyQuantumDelta embeds a factor-local quantum delta into a product vector.
pub fn copyQuantumDelta(delta: []const i32, offset: usize, width: usize, out: []i32) ![]const i32 {
    if (offset + delta.len > width or out.len < width) return Error.ContextTooSmall;
    @memset(out[0..width], 0);
    for (delta, 0..) |value, index| out[offset + index] = value;
    return out[0..width];
}

/// zeroSeed writes one neutral vacuum seed into caller storage.
pub fn zeroSeed(width: usize, seeds: []Seed, quantum_storage: []i32) ![]const Seed {
    if (seeds.len < 1 or quantum_storage.len < width) return Error.ContextTooSmall;
    @memset(quantum_storage[0..width], 0);
    seeds[0] = .{ .quantum_values = quantum_storage[0..width] };
    return seeds[0..1];
}

/// copySeed embeds one factor seed into a product quantum vector.
pub fn copySeed(seed: Seed, offset: usize, width: usize, quantum_out: []i32) !Seed {
    _ = try copyQuantumDelta(seed.quantum_values, offset, width, quantum_out);
    return .{
        .id = seed.id,
        .weight_ticks = seed.weight_ticks,
        .component_weight_ticks = seed.component_weight_ticks,
        .quantum_values = quantum_out[0..width],
        .body_kind = seed.body_kind,
        .body = seed.body,
    };
}

fn TextSink(comptime Writer: type) type {
    return struct {
        const Self = @This();

        writer: Writer,
        options: RenderOptions,
        table: RenderTable,
        count: usize = 0,

        fn writeAll(self: *Self, bytes: []const u8) !void {
            try self.writer.writeAll(bytes);
        }

        fn writeFmt(self: *Self, comptime fmt: []const u8, args: anytype) !void {
            var buffer: [256]u8 = undefined;
            const rendered = try std.fmt.bufPrint(&buffer, fmt, args);
            try self.writeAll(rendered);
        }

        fn atomDerivative(atom: RenderAtom, fallback_weight_ticks: i32) i32 {
            const weight = atom.fixed_weight_ticks orelse fallback_weight_ticks;
            const shifted = weight - atom.base_weight_ticks;
            if (shifted <= 0) return 0;
            return @divTrunc(shifted, @as(i32, @intCast(atom.derivative_step_ticks)));
        }

        fn writeDerivativeAtom(self: *Self, atom: RenderAtom, fallback_weight_ticks: i32, label: ?u16) !void {
            const derivative = atomDerivative(atom, fallback_weight_ticks);
            if (derivative == 0) {
                try self.writeAll(atom.name);
            } else if (derivative == 1) {
                try self.writeAll("d");
                try self.writeAll(atom.name);
            } else {
                try self.writeFmt("d^{}{s}", .{ derivative, atom.name });
            }
            if (atom.show_label) {
                if (label) |value| try self.writeFmt("[{}]", .{value});
            }
        }

        fn writeVector(self: *Self, values: []const i32) !void {
            try self.writeAll("[");
            for (values, 0..) |value, index| {
                if (index != 0) try self.writeAll(",");
                try self.writeFmt("{}", .{value});
            }
            try self.writeAll("]");
        }

        fn writeCompact(self: *Self, candidate: Candidate) !void {
            try self.writeFmt(
                "#{} compact p={} base_id={} base_body={} base_w={} w={} l={} base_q=",
                .{ self.count, candidate.presentation, candidate.seed, candidate.seed_body, candidate.base_weight_ticks, candidate.weight_ticks, candidate.level_ticks },
            );
            try self.writeVector(candidate.base_quantum_values);
            try self.writeAll(" q=");
            try self.writeVector(candidate.quantum_values);
            try self.writeAll(" base_cw=");
            try self.writeVector(candidate.base_component_weight_ticks);
            try self.writeAll(" cw=");
            try self.writeVector(candidate.component_weight_ticks);
            try self.writeAll(" modes=[");
            for (candidate.modes, 0..) |mode, index| {
                if (index != 0) try self.writeAll(", ");
                try self.writeFmt(
                    "{{i={},id={},c={},label={},w={},body={}}}",
                    .{ mode.mode_index, mode.id, mode.component, mode.label, mode.weight_ticks, mode.body },
                );
            }
            try self.writeAll("]\n");
        }

        fn candidateSeedMask(candidate: Candidate) u32 {
            return candidate.seed_body;
        }

        fn writeSeedStateAtoms(self: *Self, seed_mask: u32, written: *usize) !void {
            var bit: usize = 0;
            while (bit < @bitSizeOf(u32)) : (bit += 1) {
                if ((seed_mask & (@as(u32, 1) << @intCast(bit))) == 0) continue;
                const atom = self.table.seedBitAtom(bit) orelse continue;
                if (written.* != 0) try self.writeAll("; ");
                try self.writeDerivativeAtom(atom, 0, null);
                written.* += 1;
            }
        }

        fn writeState(self: *Self, candidate: Candidate) !void {
            try self.writeFmt("#{} |", .{self.count});
            var written: usize = 0;
            try self.writeSeedStateAtoms(candidateSeedMask(candidate), &written);
            if (written == 0 and (candidate.seed != 0 or candidate.seed_body != 0)) {
                try self.writeFmt("base{}", .{candidate.seed});
                written += 1;
            }
            for (candidate.modes) |mode| {
                if (written != 0) try self.writeAll("; ");
                if (self.table.modeAtom(mode.id, mode.component)) |atom| {
                    try self.writeDerivativeAtom(atom, @intCast(mode.weight_ticks), mode.label);
                } else {
                    try self.writeFmt("mode{}[{}]", .{ mode.id, mode.label });
                }
                try self.writeFmt("_-{}", .{mode.weight_ticks});
                if (mode.component != 0) try self.writeFmt("@{}", .{mode.component});
                written += 1;
            }
            if (written == 0) try self.writeAll("vacuum");
            try self.writeAll(">\n");
        }

        fn writeSeedOperators(self: *Self, seed_mask: u32, written: *usize) !void {
            var bit: usize = 0;
            while (bit < @bitSizeOf(u32)) : (bit += 1) {
                if ((seed_mask & (@as(u32, 1) << @intCast(bit))) == 0) continue;
                const atom = self.table.seedBitAtom(bit) orelse continue;
                if (written.* != 0) try self.writeAll(" ");
                try self.writeDerivativeAtom(atom, 0, null);
                try self.writeAll("(");
                try self.writeAll(self.options.insertion);
                try self.writeAll(")");
                written.* += 1;
            }
        }

        fn writeModeOperators(self: *Self, candidate: Candidate, written: *usize) !void {
            for (candidate.modes) |mode| {
                if (written.* != 0) try self.writeAll(" ");
                if (self.table.modeAtom(mode.id, mode.component)) |atom| {
                    try self.writeDerivativeAtom(atom, @intCast(mode.weight_ticks), mode.label);
                } else {
                    try self.writeFmt("op{}", .{mode.id});
                    if (mode.label != 0) try self.writeFmt("[{}]", .{mode.label});
                }
                try self.writeAll("(");
                try self.writeAll(self.options.insertion);
                try self.writeAll(")");
                written.* += 1;
            }
        }

        fn writeOperator(self: *Self, candidate: Candidate) !void {
            try self.writeFmt("#{} :", .{self.count});
            var written: usize = 0;
            try self.writeSeedOperators(candidateSeedMask(candidate), &written);
            try self.writeModeOperators(candidate, &written);
            if (written == 0) try self.writeAll("1");
            try self.writeAll(":\n");
        }

        /// emitBasisState writes one candidate and never retains it.
        pub fn emitBasisState(self: *Self, candidate: Candidate) !void {
            if (self.count >= self.options.max_states) return;
            switch (self.options.format) {
                .compact => try self.writeCompact(candidate),
                .state => try self.writeState(candidate),
                .operator_at_zero => try self.writeOperator(candidate),
            }
            self.count += 1;
        }
    };
}
fn fnv(hash: u64, value: anytype) u64 {
    var h = hash;
    const T = @TypeOf(value);
    const bytes = std.mem.asBytes(&@as(T, value));
    for (bytes) |byte| h = (h ^ byte) *% 1099511628211;
    return h;
}

const OperatorAtomHash = struct {
    head: u64,
    flags: u64,
    body: u64,
};

fn operatorAtomHashParts(atom: OperatorAtom) OperatorAtomHash {
    var head = @as(u64, atom.field);
    head |= @as(u64, atom.component) << 32;
    head |= @as(u64, atom.derivative) << 48;

    var flags = @as(u64, atom.label);
    flags |= @as(u64, @as(u32, @bitCast(atom.weight_ticks))) << 16;
    flags ^= @as(u64, @intFromEnum(atom.statistics)) << 48;
    flags ^= @as(u64, @intFromEnum(atom.source)) << 56;

    return .{ .head = head, .flags = flags, .body = atom.body };
}

fn appendOperatorAtomHash(hash: u64, parts: OperatorAtomHash) u64 {
    var h = mixHash(hash, parts.head);
    h = mixHash(h, parts.flags);
    h = mixHash(h, parts.body);
    return h;
}

fn hashOperatorAtom(hash: u64, atom: OperatorAtom) u64 {
    return appendOperatorAtomHash(hash, operatorAtomHashParts(atom));
}

fn mixHash(hash: u64, value: u64) u64 {
    return (hash *% 0x9e3779b185ebca87) +% value +% 0x632be59bd9b4e019;
}

fn mixSignedHash(hash: u64, value: i32) u64 {
    return mixHash(hash, @as(u32, @bitCast(value)));
}

fn operatorRecordHashPrefixFromValues(
    presentation_id: u16,
    seed_id: u16,
    seed_body: u32,
    base_weight_ticks: i32,
    total_weight_ticks: i32,
    level_ticks: u32,
    base_quantum_values: []const i32,
    quantum_values: []const i32,
) u64 {
    var hash: u64 = 14695981039346656037;
    hash = mixHash(hash, presentation_id);
    hash = mixHash(hash, seed_id);
    hash = mixHash(hash, seed_body);
    hash = mixSignedHash(hash, base_weight_ticks);
    hash = mixSignedHash(hash, total_weight_ticks);
    hash = mixHash(hash, level_ticks);
    for (base_quantum_values) |value| hash = mixSignedHash(hash, value);
    for (quantum_values) |value| hash = mixSignedHash(hash, value);
    return hash;
}

fn operatorRecordHashPrefix(
    presentation_id: u16,
    seed: Seed,
    total_weight_ticks: i32,
    level_ticks: u32,
    quantum_values: []const i32,
    base_atoms: []const OperatorAtom,
) u64 {
    var hash = operatorRecordHashPrefixFromValues(
        presentation_id,
        seed.id,
        seed.body,
        seed.weight_ticks,
        total_weight_ticks,
        level_ticks,
        seed.quantum_values,
        quantum_values,
    );
    for (base_atoms) |atom| hash = hashOperatorAtom(hash, atom);
    return hash;
}

fn derivativeOrder(base_weight_ticks: i32, derivative_step_ticks: u32, weight_ticks: i32) u16 {
    if (derivative_step_ticks == 0 or weight_ticks <= base_weight_ticks) return 0;
    return @intCast(@divTrunc(weight_ticks - base_weight_ticks, @as(i32, @intCast(derivative_step_ticks))));
}

fn operatorAtomFromMode(mode: Mode) OperatorAtom {
    return .{
        .field = mode.id,
        .component = mode.component,
        .derivative = derivativeOrder(mode.base_weight_ticks, mode.derivative_step_ticks, @intCast(mode.weight_ticks)),
        .label = mode.label,
        .weight_ticks = @intCast(mode.weight_ticks),
        .body = mode.body,
        .statistics = mode.statistics,
        .source = .descendant,
    };
}

fn operatorAtomFromModeEntry(mode: ModeEntry) OperatorAtom {
    return .{
        .field = mode.id,
        .component = mode.component,
        .derivative = derivativeOrder(mode.base_weight_ticks, mode.derivative_step_ticks, @intCast(mode.weight_ticks)),
        .label = mode.label,
        .weight_ticks = @intCast(mode.weight_ticks),
        .body = mode.body,
        .statistics = mode.statistics,
        .source = .descendant,
    };
}

fn appendSeedMaskAtoms(seed_mask: u32, atoms: []OperatorAtom) !usize {
    var written: usize = 0;
    var bit: usize = 0;
    while (bit < @bitSizeOf(u32)) : (bit += 1) {
        if ((seed_mask & (@as(u32, 1) << @intCast(bit))) == 0) continue;
        if (written >= atoms.len) return Error.ContextTooSmall;
        atoms[written] = .{
            .field = @intCast(bit),
            .body = @as(u32, 1) << @intCast(bit),
            .statistics = .fermionic,
            .source = .seed,
        };
        written += 1;
    }
    return written;
}

fn appendSeedAtoms(candidate: Candidate, atoms: []OperatorAtom) !usize {
    return appendSeedMaskAtoms(candidate.seed_body, atoms);
}

fn appendSeedRecordAtoms(seed: Seed, atoms: []OperatorAtom) !usize {
    switch (seed.body_kind) {
        .finite_mask => return appendSeedMaskAtoms(seed.body, atoms),
        .primary => {
            if (seed.body != 0) return Error.InvalidDescriptor;
        },
        .none => if (seed.body != 0) return appendSeedMaskAtoms(seed.body, atoms),
    }
    if (seed.id == 0) return 0;
    if (atoms.len == 0) return Error.ContextTooSmall;
    atoms[0] = .{
        .field = seed.id,
        .statistics = .bosonic,
        .source = .seed,
    };
    return 1;
}

fn lowerCandidateToOperatorRecord(candidate: Candidate, context: *OperatorContext) !OperatorRecord {
    var written = try appendSeedAtoms(candidate, context.atoms);
    const descendant_start = written;
    if (context.atoms.len - written < candidate.modes.len) return Error.ContextTooSmall;
    for (candidate.modes) |mode| {
        context.atoms[written] = operatorAtomFromModeEntry(mode);
        written += 1;
    }

    return .{
        .presentation = candidate.presentation,
        .seed = candidate.seed,
        .seed_body = candidate.seed_body,
        .base_atoms = context.atoms[0..descendant_start],
        .descendant_atoms = context.atoms[descendant_start..written],
        .base_weight_ticks = candidate.base_weight_ticks,
        .weight_ticks = candidate.weight_ticks,
        .level_ticks = candidate.level_ticks,
        .base_quantum_values = candidate.base_quantum_values,
        .quantum_values = candidate.quantum_values,
        .base_component_weight_ticks = candidate.base_component_weight_ticks,
        .component_weight_ticks = candidate.component_weight_ticks,
    };
}

fn tableIndex(mode_count: usize, max_ticks: u32, quantum_count: usize, order: usize, remaining: u32, slot: usize) usize {
    _ = mode_count;
    return ((order * (@as(usize, max_ticks) + 1) + @as(usize, remaining)) * quantum_count) + slot;
}

fn quantumDelta(mode: Mode, slot: usize) i32 {
    if (slot >= mode.quantum_delta.len) return 0;
    return mode.quantum_delta[slot];
}

fn quantumDeltaFromSlice(delta: []const i32, slot: usize) i32 {
    if (slot >= delta.len) return 0;
    return delta[slot];
}

fn normalizeMod(value: i32, modulus: u8) u6 {
    const raw = @mod(value, @as(i32, modulus));
    return @intCast(raw);
}

fn shiftedFiniteBits(bits: u64, delta: i32, modulus: u8) u64 {
    var shifted: u64 = 0;
    var value: u8 = 0;
    const normalized = normalizeMod(delta, modulus);
    while (value < modulus) : (value += 1) {
        if ((bits & (@as(u64, 1) << @intCast(value))) == 0) continue;
        const next = (value + normalized) % modulus;
        shifted |= @as(u64, 1) << @intCast(next);
    }
    return shifted;
}

fn slotModulus(quantum: Quantum) !u8 {
    return switch (quantum.kind) {
        .additive => 0,
        .zn => if (quantum.modulus > 0 and quantum.modulus <= 64) quantum.modulus else Error.UnsupportedQuantumFilter,
        .tensor_rep => Error.UnsupportedQuantumFilter,
    };
}

fn validateQuantum(quantum: Quantum) !void {
    switch (quantum.kind) {
        .additive, .tensor_rep => {},
        .zn => if (quantum.modulus == 0 or quantum.modulus > 64) return Error.UnsupportedQuantumFilter,
    }
}

fn filterSupported(quantum: Quantum) bool {
    return switch (quantum.kind) {
        .additive, .zn => true,
        .tensor_rep => false,
    };
}

fn quantumDeltaSupported(quantum: Quantum, delta: i32) bool {
    return switch (quantum.kind) {
        .additive, .zn => true,
        .tensor_rep => delta == 0,
    };
}

fn seedLevelBudget(query: Query, seed: Seed) ?u32 {
    const limit = query.weightLimit();
    if (seed.weight_ticks > limit) return null;
    return @intCast(limit - seed.weight_ticks);
}

fn maxLevelBudget(presentation: Presentation, query: Query) u32 {
    var max_budget: u32 = 0;
    for (presentation.seeds) |seed| {
        if (seedLevelBudget(query, seed)) |budget| {
            if (budget > max_budget) max_budget = budget;
        }
    }
    return max_budget;
}

fn validate(presentation: Presentation, query: Query, context: *Context, needs_suffix_admissibility: bool, word_capacity: usize) !void {
    const quantum_count = presentation.quantum_schema.len;
    if (context.quantum_values.len < quantum_count) return Error.ContextTooSmall;
    if (query.level_match) |filter| {
        const required = @max(filter.left_component, filter.right_component) + 1;
        if (context.component_weights.len < required) return Error.ContextTooSmall;
    }

    for (presentation.quantum_schema) |quantum| try validateQuantum(quantum);
    for (presentation.modes) |mode| {
        if (mode.weight_ticks == 0) return Error.InvalidDescriptor;
        if (mode.quantum_delta.len != 0 and mode.quantum_delta.len < quantum_count) return Error.InvalidDescriptor;
        for (presentation.quantum_schema, 0..) |quantum, slot| {
            if (!quantumDeltaSupported(quantum, quantumDelta(mode, slot))) return Error.UnsupportedQuantumFilter;
        }
    }
    for (presentation.seeds) |seed| {
        if (seed.quantum_values.len != 0 and seed.quantum_values.len < quantum_count) return Error.InvalidDescriptor;
        if (seed.body_kind == .primary and seed.body != 0) return Error.InvalidDescriptor;
    }
    for (query.quantum_filters) |filter| {
        if (filter.slot >= quantum_count) return Error.InvalidQuery;
        if (!filterSupported(presentation.quantum_schema[filter.slot])) return Error.UnsupportedQuantumFilter;
    }

    if (needs_suffix_admissibility) {
        const slots = Context.reachabilitySlots(presentation.modes.len, maxLevelBudget(presentation, query), quantum_count);
        if (context.add_min.len < slots or context.add_max.len < slots or context.finite_bits.len < slots) return Error.ContextTooSmall;
    }
    if (query.max_word_length > word_capacity) return Error.WordStackTooSmall;
}

fn buildReachability(presentation: Presentation, max_budget: u32, context: *Context) !void {
    const mode_count = presentation.modes.len;
    const quantum_count = presentation.quantum_schema.len;

    var remaining: u32 = 0;
    while (remaining <= max_budget) : (remaining += 1) {
        for (presentation.quantum_schema, 0..) |quantum, slot| {
            const index = tableIndex(mode_count, max_budget, quantum_count, mode_count, remaining, slot);
            context.add_min[index] = 0;
            context.add_max[index] = 0;
            _ = quantum;
            context.finite_bits[index] = 1;
        }
    }

    var order = mode_count;
    while (order > 0) {
        order -= 1;
        const mode = presentation.modes[order];
        remaining = 0;
        while (remaining <= max_budget) : (remaining += 1) {
            for (presentation.quantum_schema, 0..) |quantum, slot| {
                const index = tableIndex(mode_count, max_budget, quantum_count, order, remaining, slot);
                const skip = tableIndex(mode_count, max_budget, quantum_count, order + 1, remaining, slot);
                context.add_min[index] = context.add_min[skip];
                context.add_max[index] = context.add_max[skip];
                context.finite_bits[index] = context.finite_bits[skip];

                if (mode.weight_ticks > remaining) continue;
                const next_order = if (mode.statistics == .bosonic) order else order + 1;
                const next_remaining = remaining - mode.weight_ticks;
                const take = tableIndex(mode_count, max_budget, quantum_count, next_order, next_remaining, slot);
                const delta = quantumDelta(mode, slot);

                switch (quantum.kind) {
                    .additive => {
                        context.add_min[index] = @min(context.add_min[index], delta + context.add_min[take]);
                        context.add_max[index] = @max(context.add_max[index], delta + context.add_max[take]);
                    },
                    .zn => {
                        const modulus = try slotModulus(quantum);
                        context.finite_bits[index] |= shiftedFiniteBits(context.finite_bits[take], delta, modulus);
                    },
                    .tensor_rep => {},
                }
            }
        }
    }
}

fn filterMatches(quantum: Quantum, current: i32, target: i32) !bool {
    return switch (quantum.kind) {
        .additive => current == target,
        .zn => blk: {
            const modulus = try slotModulus(quantum);
            break :blk normalizeMod(current - target, modulus) == 0;
        },
        .tensor_rep => Error.UnsupportedQuantumFilter,
    };
}

fn loadSeedComponentWeights(context: *Context, seed: Seed) void {
    if (context.component_weights.len == 0) return;
    @memset(context.component_weights, 0);
    if (seed.component_weight_ticks.len == 0) {
        context.component_weights[0] = seed.weight_ticks;
        return;
    }
    const count = @min(context.component_weights.len, seed.component_weight_ticks.len);
    for (seed.component_weight_ticks[0..count], 0..) |weight, component| {
        context.component_weights[component] = weight;
    }
}

fn levelMatchPrefixPossible(query: Query, context: *Context, remaining: u32) bool {
    const filter = query.level_match orelse return true;
    const left = context.component_weights[filter.left_component];
    const right = context.component_weights[filter.right_component];
    const diff = if (left > right) left - right else right - left;
    return diff <= @as(i32, @intCast(remaining));
}

fn suffixAdmissible(presentation: Presentation, query: Query, context: *Context, max_budget: u32, seed_budget: u32, order: usize, current_level: u32) !bool {
    if (current_level > seed_budget) return false;
    const remaining = seed_budget - current_level;
    if (!levelMatchPrefixPossible(query, context, remaining)) return false;
    const quantum_count = presentation.quantum_schema.len;

    if (query.quantum_filters.len == 1) {
        return suffixFilterAdmissible(presentation, context, max_budget, quantum_count, order, remaining, query.quantum_filters[0]);
    }
    for (query.quantum_filters) |filter| {
        if (!try suffixFilterAdmissible(presentation, context, max_budget, quantum_count, order, remaining, filter)) return false;
    }
    return true;
}

fn suffixFilterAdmissible(presentation: Presentation, context: *Context, max_budget: u32, quantum_count: usize, order: usize, remaining: u32, filter: QuantumFilter) !bool {
    const slot = filter.slot;
    const quantum = presentation.quantum_schema[slot];
    const index = tableIndex(presentation.modes.len, max_budget, quantum_count, order, remaining, slot);
    const current = context.quantum_values[slot];
    switch (quantum.kind) {
        .additive => {
            const need = filter.value - current;
            return need >= context.add_min[index] and need <= context.add_max[index];
        },
        .zn => {
            const modulus = try slotModulus(quantum);
            const need = normalizeMod(filter.value - current, modulus);
            return (context.finite_bits[index] & (@as(u64, 1) << need)) != 0;
        },
        .tensor_rep => return Error.UnsupportedQuantumFilter,
    }
}

fn shouldEmit(presentation: Presentation, query: Query, context: *Context, _: Seed, _: []const ModeEntry, current_weight: i32) !bool {
    switch (query.weight) {
        .exact => |ticks| if (current_weight != ticks) return false,
        .max => |ticks| if (current_weight > ticks) return false,
    }
    if (query.level_match) |filter| {
        if (context.component_weights[filter.left_component] != context.component_weights[filter.right_component]) return false;
    }
    if (query.quantum_filters.len == 1) {
        const filter = query.quantum_filters[0];
        return filterMatches(presentation.quantum_schema[filter.slot], context.quantum_values[filter.slot], filter.value);
    }
    for (query.quantum_filters) |filter| {
        if (!try filterMatches(presentation.quantum_schema[filter.slot], context.quantum_values[filter.slot], filter.value)) return false;
    }
    return true;
}

fn queryNeedsSuffixAdmissibility(query: Query) bool {
    return query.level_match != null or query.quantum_filters.len != 0;
}

fn addModeQuantum(presentation: Presentation, context: *Context, mode: Mode, sign: i32) void {
    switch (presentation.quantum_schema.len) {
        0 => {},
        1 => context.quantum_values[0] += sign * quantumDelta(mode, 0),
        else => {
            for (0..presentation.quantum_schema.len) |slot| {
                context.quantum_values[slot] += sign * quantumDelta(mode, slot);
            }
        },
    }
    if (mode.component < context.component_weights.len) {
        context.component_weights[mode.component] += sign * @as(i32, @intCast(mode.weight_ticks));
    }
}

fn streamFrom(
    comptime needs_suffix_admissibility: bool,
    presentation: Presentation,
    query: Query,
    context: *Context,
    seed: Seed,
    max_budget: u32,
    seed_budget: u32,
    start_order: usize,
    current_level: u32,
    depth: usize,
    sink: anytype,
) anyerror!void {
    const current_weight = seed.weight_ticks + @as(i32, @intCast(current_level));
    if (try shouldEmit(presentation, query, context, seed, context.word[0..depth], current_weight)) {
        try sink.emitBasisState(Candidate{
            .presentation = presentation.id,
            .seed = seed.id,
            .seed_body = seed.body,
            .base_weight_ticks = seed.weight_ticks,
            .base_component_weight_ticks = seed.component_weight_ticks,
            .base_quantum_values = seed.quantum_values,
            .weight_ticks = current_weight,
            .level_ticks = current_level,
            .component_weight_ticks = context.component_weights,
            .quantum_values = context.quantum_values[0..presentation.quantum_schema.len],
            .modes = context.word[0..depth],
        });
    }

    if (depth >= query.max_word_length) return;

    var order = start_order;
    while (order < presentation.modes.len) : (order += 1) {
        const mode = presentation.modes[order];
        if (mode.weight_ticks > seed_budget - current_level) continue;
        const next_level = current_level + mode.weight_ticks;
        const next_order = if (mode.statistics == .bosonic) order else order + 1;

        addModeQuantum(presentation, context, mode, 1);
        if (!needs_suffix_admissibility or try suffixAdmissible(presentation, query, context, max_budget, seed_budget, next_order, next_level)) {
            context.word[depth] = .{
                .mode_index = @intCast(order),
                .id = mode.id,
                .component = mode.component,
                .label = mode.label,
                .weight_ticks = mode.weight_ticks,
                .base_weight_ticks = mode.base_weight_ticks,
                .derivative_step_ticks = mode.derivative_step_ticks,
                .statistics = mode.statistics,
                .body = mode.body,
            };
            try streamFrom(needs_suffix_admissibility, presentation, query, context, seed, max_budget, seed_budget, next_order, next_level, depth + 1, sink);
        }
        addModeQuantum(presentation, context, mode, -1);
    }
}

/// stream enumerates compact basis candidates without retaining emitted states.
pub fn stream(presentation: Presentation, query: Query, context: *Context, sink: anytype) !void {
    const needs_suffix_admissibility = queryNeedsSuffixAdmissibility(query);
    try validate(presentation, query, context, needs_suffix_admissibility, context.word.len);
    const max_budget = maxLevelBudget(presentation, query);
    if (needs_suffix_admissibility) try buildReachability(presentation, max_budget, context);

    for (presentation.seeds) |seed| {
        const seed_budget = seedLevelBudget(query, seed) orelse continue;
        for (0..presentation.quantum_schema.len) |slot| {
            context.quantum_values[slot] = if (slot < seed.quantum_values.len) seed.quantum_values[slot] else 0;
        }
        loadSeedComponentWeights(context, seed);
        if (needs_suffix_admissibility) {
            if (!try suffixAdmissible(presentation, query, context, max_budget, seed_budget, 0, 0)) continue;
            try streamFrom(true, presentation, query, context, seed, max_budget, seed_budget, 0, 0, 0, sink);
        } else {
            try streamFrom(false, presentation, query, context, seed, max_budget, seed_budget, 0, 0, 0, sink);
        }
    }
}

fn emitGenericOperatorRecord(
    presentation: Presentation,
    seed: Seed,
    base_count: usize,
    current_weight: i32,
    current_level: u32,
    structural_hash: u64,
    context: *Context,
    operator_context: *OperatorContext,
    depth: usize,
    sink: anytype,
) !void {
    try sink.emitOperatorRecord(OperatorRecord{
        .presentation = presentation.id,
        .seed = seed.id,
        .seed_body = seed.body,
        .base_atoms = operator_context.atoms[0..base_count],
        .descendant_atoms = operator_context.atoms[base_count..depth],
        .base_weight_ticks = seed.weight_ticks,
        .weight_ticks = current_weight,
        .level_ticks = current_level,
        .base_quantum_values = seed.quantum_values,
        .quantum_values = context.quantum_values[0..presentation.quantum_schema.len],
        .base_component_weight_ticks = seed.component_weight_ticks,
        .component_weight_ticks = context.component_weights,
        .structural_hash = structural_hash,
    });
}

fn streamOperatorFrom(
    comptime needs_suffix_admissibility: bool,
    presentation: Presentation,
    query: Query,
    context: *Context,
    operator_context: *OperatorContext,
    seed: Seed,
    max_budget: u32,
    seed_budget: u32,
    base_count: usize,
    start_order: usize,
    current_level: u32,
    depth: usize,
    max_depth: usize,
    structural_hash: u64,
    sink: anytype,
) anyerror!void {
    const current_weight = seed.weight_ticks + @as(i32, @intCast(current_level));
    if (try shouldEmit(presentation, query, context, seed, &.{}, current_weight)) {
        try emitGenericOperatorRecord(
            presentation,
            seed,
            base_count,
            current_weight,
            current_level,
            structural_hash,
            context,
            operator_context,
            depth,
            sink,
        );
    }

    if (depth - base_count >= max_depth) return;

    var order = start_order;
    while (order < presentation.modes.len) : (order += 1) {
        const mode = presentation.modes[order];
        if (mode.weight_ticks > seed_budget - current_level) continue;
        const next_level = current_level + mode.weight_ticks;
        const next_order = if (mode.statistics == .bosonic) order else order + 1;

        addModeQuantum(presentation, context, mode, 1);
        if (!needs_suffix_admissibility or try suffixAdmissible(presentation, query, context, max_budget, seed_budget, next_order, next_level)) {
            if (depth >= operator_context.atoms.len) return Error.ContextTooSmall;
            operator_context.atoms[depth] = operatorAtomFromMode(mode);
            const next_hash = if (structural_hash == 0) 0 else appendOperatorAtomHash(structural_hash, operatorAtomHashParts(operator_context.atoms[depth]));
            try streamOperatorFrom(
                needs_suffix_admissibility,
                presentation,
                query,
                context,
                operator_context,
                seed,
                max_budget,
                seed_budget,
                base_count,
                next_order,
                next_level,
                depth + 1,
                max_depth,
                next_hash,
                sink,
            );
        }
        addModeQuantum(presentation, context, mode, -1);
    }
}

fn streamGenericOperatorRecords(presentation: Presentation, query: Query, context: *Context, operator_context: *OperatorContext, sink: anytype) !void {
    const needs_suffix_admissibility = queryNeedsSuffixAdmissibility(query);
    try validate(presentation, query, context, needs_suffix_admissibility, query.max_word_length);
    const max_budget = maxLevelBudget(presentation, query);
    if (needs_suffix_admissibility) try buildReachability(presentation, max_budget, context);

    for (presentation.seeds) |seed| {
        const seed_budget = seedLevelBudget(query, seed) orelse continue;
        for (0..presentation.quantum_schema.len) |slot| {
            context.quantum_values[slot] = if (slot < seed.quantum_values.len) seed.quantum_values[slot] else 0;
        }
        loadSeedComponentWeights(context, seed);

        const base_count = try appendSeedRecordAtoms(seed, operator_context.atoms);
        if (operator_context.atoms.len - base_count < query.max_word_length) return Error.ContextTooSmall;
        if (needs_suffix_admissibility) {
            if (!try suffixAdmissible(presentation, query, context, max_budget, seed_budget, 0, 0)) continue;
            try streamOperatorFrom(true, presentation, query, context, operator_context, seed, max_budget, seed_budget, base_count, 0, 0, base_count, query.max_word_length, 0, sink);
        } else {
            try streamOperatorFrom(false, presentation, query, context, operator_context, seed, max_budget, seed_budget, base_count, 0, 0, base_count, query.max_word_length, 0, sink);
        }
    }
}

fn CompactOperatorAdapter(comptime Sink: type) type {
    return struct {
        const Self = @This();

        operator_context: *OperatorContext,
        sink: Sink,

        pub fn emitBasisState(self: *Self, candidate: Candidate) !void {
            const record = try lowerCandidateToOperatorRecord(candidate, self.operator_context);
            try self.sink.emitOperatorRecord(record);
        }
    };
}

fn canStreamBosonicOperatorOccupations(presentation: Presentation, query: Query) bool {
    if (presentation.quantum_schema.len != 0) return false;
    if (query.quantum_filters.len != 0 or query.level_match != null) return false;
    if (presentation.seeds.len != 1) return false;
    const seed = presentation.seeds[0];
    if (seed.id != 0 or seed.body != 0 or seed.weight_ticks != 0) return false;
    if (seed.quantum_values.len != 0 or seed.component_weight_ticks.len != 0) return false;
    for (presentation.modes) |mode| {
        if (mode.statistics != .bosonic) return false;
        if (mode.weight_ticks == 0) return false;
    }
    return true;
}

fn emitBosonicOperatorOccupations(
    presentation: Presentation,
    output_level: u32,
    target_level: u32,
    start_order: usize,
    depth: usize,
    max_depth: usize,
    context: *OperatorContext,
    sink: anytype,
) anyerror!void {
    if (target_level == 0) {
        try sink.emitOperatorRecord(OperatorRecord{
            .presentation = presentation.id,
            .seed = 0,
            .seed_body = 0,
            .descendant_atoms = context.atoms[0..depth],
            .weight_ticks = @intCast(output_level),
            .level_ticks = output_level,
        });
        return;
    }
    if (depth >= max_depth) return;

    var order = start_order;
    while (order < presentation.modes.len) : (order += 1) {
        const mode = presentation.modes[order];
        if (mode.weight_ticks > target_level) continue;
        if (depth >= context.atoms.len) return Error.ContextTooSmall;
        context.atoms[depth] = operatorAtomFromMode(mode);
        try emitBosonicOperatorOccupations(
            presentation,
            output_level,
            target_level - mode.weight_ticks,
            order,
            depth + 1,
            max_depth,
            context,
            sink,
        );
    }
}

fn streamBosonicOperatorOccupations(presentation: Presentation, query: Query, context: *OperatorContext, sink: anytype) !void {
    const limit = query.weightLimit();
    if (limit < 0) return;
    const max_level: u32 = @intCast(limit);
    const max_depth = @min(@as(usize, query.max_word_length), context.atoms.len);
    var level: u32 = switch (query.weight) {
        .exact => max_level,
        .max => 0,
    };
    while (level <= max_level) : (level += 1) {
        try emitBosonicOperatorOccupations(presentation, level, level, 0, 0, max_depth, context, sink);
        switch (query.weight) {
            .exact => break,
            .max => {},
        }
    }
}

fn isNeutralBosonicMode(presentation: Presentation, mode: Mode) bool {
    if (mode.weight_ticks == 0 or mode.statistics != .bosonic) return false;
    for (0..presentation.quantum_schema.len) |slot| {
        if (quantumDelta(mode, slot) != 0) return false;
    }
    return true;
}

fn chargedFermionDelta(presentation: Presentation, mode: Mode, slot: usize) ?i32 {
    if (mode.weight_ticks == 0 or mode.statistics != .fermionic) return null;
    const delta = quantumDelta(mode, slot);
    if (delta == 0) return null;
    for (0..presentation.quantum_schema.len) |index| {
        if (index != slot and quantumDelta(mode, index) != 0) return null;
    }
    return delta;
}

fn isPlannedChargedFermion(presentation: Presentation, mode: Mode, plan: NeutralChargedPlan) bool {
    const delta = chargedFermionDelta(presentation, mode, plan.charge_slot) orelse return false;
    return delta == plan.charged_delta;
}

const NeutralChargedPlan = struct {
    charge_slot: u8,
    charged_delta: i32,
};

fn singleAdditiveExactQuerySlot(presentation: Presentation, query: Query) ?u8 {
    if (query.quantum_filters.len != 1) return null;
    const slot = query.quantum_filters[0].slot;
    if (slot >= presentation.quantum_schema.len) return null;
    if (presentation.quantum_schema[slot].kind != .additive) return null;
    switch (query.weight) {
        .exact => {},
        .max => return null,
    }
    return slot;
}

fn neededChargedCount(seed_charge: i32, target_charge: i32, charged_delta: i32) ?usize {
    const total_delta = target_charge - seed_charge;
    if (@rem(total_delta, charged_delta) != 0) return null;
    const count = @divTrunc(total_delta, charged_delta);
    if (count < 0) return null;
    return @intCast(count);
}

fn seedCharge(seed: Seed, slot: usize) i32 {
    return if (slot < seed.quantum_values.len) seed.quantum_values[slot] else 0;
}

fn writeTargetQuantumValues(presentation: Presentation, query: Query, plan: NeutralChargedPlan, seed: Seed, context: *Context) ![]const i32 {
    const quantum_count = presentation.quantum_schema.len;
    if (context.quantum_values.len < quantum_count) return Error.ContextTooSmall;
    for (0..quantum_count) |slot| {
        context.quantum_values[slot] = if (slot < seed.quantum_values.len) seed.quantum_values[slot] else 0;
    }
    context.quantum_values[plan.charge_slot] = query.quantum_filters[0].value;
    return context.quantum_values[0..quantum_count];
}

fn appendOperatorMode(mode: Mode, modes: []Mode, atoms: []OperatorAtom, hashes: []OperatorAtomHash, written: *usize) !void {
    if (written.* >= modes.len or written.* >= atoms.len or written.* >= hashes.len) return Error.ContextTooSmall;
    modes[written.*] = mode;
    atoms[written.*] = operatorAtomFromMode(mode);
    hashes[written.*] = operatorAtomHashParts(atoms[written.*]);
    written.* += 1;
}

fn neutralChargedPlan(presentation: Presentation, query: Query) ?NeutralChargedPlan {
    const charge_slot = singleAdditiveExactQuerySlot(presentation, query) orelse return null;
    if (query.level_match != null) return null;

    var neutral_count: usize = 0;
    var charged_count: usize = 0;
    var charged_delta: ?i32 = null;
    for (presentation.modes) |mode| {
        if (isNeutralBosonicMode(presentation, mode)) {
            neutral_count += 1;
        } else if (chargedFermionDelta(presentation, mode, charge_slot)) |delta| {
            if (charged_delta) |existing| {
                if (existing != delta) return null;
            } else {
                charged_delta = delta;
            }
            charged_count += 1;
        } else {
            return null;
        }
    }
    if (neutral_count == 0 or charged_count == 0) return null;
    const delta = charged_delta orelse return null;

    for (presentation.seeds) |seed| {
        const seed_budget = seedLevelBudget(query, seed) orelse continue;
        if (seed_budget > operator_join_max_level) return null;
        const count = neededChargedCount(seedCharge(seed, charge_slot), query.quantum_filters[0].value, delta) orelse continue;
        if (count > 4) return null;
    }

    return .{ .charge_slot = charge_slot, .charged_delta = delta };
}

const operator_join_max_level = 96;
const operator_join_max_modes = 128;
const operator_join_max_charged_fragments = 65536;

const ChargedFragment = struct {
    first: u16 = 0,
    second: u16 = 0,
    third: u16 = 0,
    fourth: u16 = 0,
    count: u8 = 0,
};

const ChargedAppend = struct {
    depth: usize,
    hash: u64,
};

fn appendChargedAtom(atom: OperatorAtom, atom_hash: OperatorAtomHash, context: *OperatorContext, depth: *usize, hash: *u64) !void {
    if (depth.* >= context.atoms.len) return Error.ContextTooSmall;
    context.atoms[depth.*] = atom;
    hash.* = appendOperatorAtomHash(hash.*, atom_hash);
    depth.* += 1;
}

fn appendChargedFragmentAtoms(
    fragment: ChargedFragment,
    charged_atoms: []const OperatorAtom,
    charged_hashes: []const OperatorAtomHash,
    context: *OperatorContext,
    depth: usize,
    structural_hash: u64,
) !ChargedAppend {
    var next_depth = depth;
    var next_hash = structural_hash;
    switch (fragment.count) {
        0 => {},
        1 => try appendChargedAtom(charged_atoms[fragment.first], charged_hashes[fragment.first], context, &next_depth, &next_hash),
        2 => {
            try appendChargedAtom(charged_atoms[fragment.first], charged_hashes[fragment.first], context, &next_depth, &next_hash);
            try appendChargedAtom(charged_atoms[fragment.second], charged_hashes[fragment.second], context, &next_depth, &next_hash);
        },
        3 => {
            try appendChargedAtom(charged_atoms[fragment.first], charged_hashes[fragment.first], context, &next_depth, &next_hash);
            try appendChargedAtom(charged_atoms[fragment.second], charged_hashes[fragment.second], context, &next_depth, &next_hash);
            try appendChargedAtom(charged_atoms[fragment.third], charged_hashes[fragment.third], context, &next_depth, &next_hash);
        },
        4 => {
            try appendChargedAtom(charged_atoms[fragment.first], charged_hashes[fragment.first], context, &next_depth, &next_hash);
            try appendChargedAtom(charged_atoms[fragment.second], charged_hashes[fragment.second], context, &next_depth, &next_hash);
            try appendChargedAtom(charged_atoms[fragment.third], charged_hashes[fragment.third], context, &next_depth, &next_hash);
            try appendChargedAtom(charged_atoms[fragment.fourth], charged_hashes[fragment.fourth], context, &next_depth, &next_hash);
        },
        else => return Error.InvalidDescriptor,
    }
    return .{ .depth = next_depth, .hash = next_hash };
}

fn chargedFragmentFromIndices(indices: []const u16) ChargedFragment {
    var fragment = ChargedFragment{ .count = @intCast(indices.len) };
    if (indices.len > 0) fragment.first = indices[0];
    if (indices.len > 1) fragment.second = indices[1];
    if (indices.len > 2) fragment.third = indices[2];
    if (indices.len > 3) fragment.fourth = indices[3];
    return fragment;
}

fn addChargedFragment(
    level: u32,
    fragment: ChargedFragment,
    heads: []i32,
    next: []i32,
    fragments: []ChargedFragment,
    count: *usize,
) !void {
    if (level >= heads.len or count.* >= fragments.len or count.* >= next.len) return Error.ContextTooSmall;
    fragments[count.*] = fragment;
    next[count.*] = heads[level];
    heads[level] = @intCast(count.*);
    count.* += 1;
}

fn buildChargedFragmentBuckets(
    charged_modes: []const Mode,
    needed_count: usize,
    seed_budget: u32,
    heads: []i32,
    next: []i32,
    fragments: []ChargedFragment,
) !usize {
    if (seed_budget >= heads.len or needed_count > 4) return Error.ContextTooSmall;
    @memset(heads[0 .. seed_budget + 1], -1);
    var count: usize = 0;

    var indices: [4]u16 = undefined;
    try buildChargedFragmentBucketsFrom(charged_modes, needed_count, seed_budget, 0, 0, 0, &indices, heads, next, fragments, &count);
    return count;
}

fn buildChargedFragmentBucketsFrom(
    charged_modes: []const Mode,
    needed_count: usize,
    seed_budget: u32,
    current_level: u32,
    start_order: usize,
    depth: usize,
    indices: *[4]u16,
    heads: []i32,
    next: []i32,
    fragments: []ChargedFragment,
    count: *usize,
) !void {
    if (depth == needed_count) {
        try addChargedFragment(current_level, chargedFragmentFromIndices(indices[0..depth]), heads, next, fragments, count);
        return;
    }

    var order = start_order;
    while (order < charged_modes.len) : (order += 1) {
        const mode = charged_modes[order];
        const next_level = current_level + mode.weight_ticks;
        if (next_level > seed_budget) continue;
        indices[depth] = @intCast(order);
        try buildChargedFragmentBucketsFrom(
            charged_modes,
            needed_count,
            seed_budget,
            next_level,
            order + 1,
            depth + 1,
            indices,
            heads,
            next,
            fragments,
            count,
        );
    }
}

fn emitNeutralChargedJoinedRecord(
    presentation: Presentation,
    seed: Seed,
    base_count: usize,
    total_weight_ticks: i32,
    seed_budget: u32,
    quantum_values: []const i32,
    depth: usize,
    structural_hash: u64,
    context: *OperatorContext,
    sink: anytype,
) anyerror!void {
    try sink.emitOperatorRecord(OperatorRecord{
        .presentation = presentation.id,
        .seed = seed.id,
        .seed_body = seed.body,
        .base_atoms = context.atoms[0..base_count],
        .descendant_atoms = context.atoms[base_count..depth],
        .base_weight_ticks = seed.weight_ticks,
        .weight_ticks = total_weight_ticks,
        .level_ticks = seed_budget,
        .base_quantum_values = seed.quantum_values,
        .quantum_values = quantum_values,
        .base_component_weight_ticks = seed.component_weight_ticks,
        .structural_hash = structural_hash,
    });
}

fn emitNeutralChargedBucket(
    presentation: Presentation,
    seed: Seed,
    base_count: usize,
    total_weight_ticks: i32,
    seed_budget: u32,
    quantum_values: []const i32,
    charged_atoms: []const OperatorAtom,
    charged_hashes: []const OperatorAtomHash,
    remaining_level: u32,
    depth: usize,
    max_descendants: usize,
    structural_hash: u64,
    heads: []const i32,
    next: []const i32,
    fragments: []const ChargedFragment,
    context: *OperatorContext,
    sink: anytype,
) anyerror!void {
    var cursor = heads[remaining_level];
    while (cursor >= 0) {
        const fragment_index: usize = @intCast(cursor);
        const fragment = fragments[fragment_index];
        if (depth - base_count + fragment.count > max_descendants) {
            cursor = next[fragment_index];
            continue;
        }
        const appended = try appendChargedFragmentAtoms(fragment, charged_atoms, charged_hashes, context, depth, structural_hash);
        try emitNeutralChargedJoinedRecord(
            presentation,
            seed,
            base_count,
            total_weight_ticks,
            seed_budget,
            quantum_values,
            appended.depth,
            appended.hash,
            context,
            sink,
        );
        cursor = next[fragment_index];
    }
}

fn emitNeutralChargedJoin(
    presentation: Presentation,
    seed: Seed,
    base_count: usize,
    total_weight_ticks: i32,
    seed_budget: u32,
    quantum_values: []const i32,
    neutral_modes: []const Mode,
    neutral_atoms: []const OperatorAtom,
    neutral_hashes: []const OperatorAtomHash,
    charged_atoms: []const OperatorAtom,
    charged_hashes: []const OperatorAtomHash,
    neutral_level: u32,
    start_order: usize,
    depth: usize,
    max_descendants: usize,
    structural_hash: u64,
    heads: []const i32,
    next: []const i32,
    fragments: []const ChargedFragment,
    context: *OperatorContext,
    sink: anytype,
) anyerror!void {
    try emitNeutralChargedBucket(
        presentation,
        seed,
        base_count,
        total_weight_ticks,
        seed_budget,
        quantum_values,
        charged_atoms,
        charged_hashes,
        seed_budget - neutral_level,
        depth,
        max_descendants,
        structural_hash,
        heads,
        next,
        fragments,
        context,
        sink,
    );

    if (neutral_level >= seed_budget) return;
    if (depth - base_count >= max_descendants) return;

    var order = start_order;
    while (order < neutral_modes.len) : (order += 1) {
        const mode = neutral_modes[order];
        const next_level = neutral_level + mode.weight_ticks;
        if (next_level > seed_budget) continue;
        if (depth >= context.atoms.len) return Error.ContextTooSmall;
        context.atoms[depth] = neutral_atoms[order];
        const next_hash = appendOperatorAtomHash(structural_hash, neutral_hashes[order]);
        try emitNeutralChargedJoin(
            presentation,
            seed,
            base_count,
            total_weight_ticks,
            seed_budget,
            quantum_values,
            neutral_modes,
            neutral_atoms,
            neutral_hashes,
            charged_atoms,
            charged_hashes,
            next_level,
            order,
            depth + 1,
            max_descendants,
            next_hash,
            heads,
            next,
            fragments,
            context,
            sink,
        );
    }
}

fn streamNeutralChargedOperatorJoin(presentation: Presentation, query: Query, plan: NeutralChargedPlan, basis_context: *Context, context: *OperatorContext, sink: anytype) !void {
    const target_weight = switch (query.weight) {
        .exact => |ticks| ticks,
        .max => unreachable,
    };
    const target_charge = query.quantum_filters[0].value;
    if (presentation.modes.len > operator_join_max_modes) return Error.ContextTooSmall;
    var mode_storage: [operator_join_max_modes]Mode = undefined;
    var mode_atoms_storage: [operator_join_max_modes]OperatorAtom = undefined;
    var mode_hash_storage: [operator_join_max_modes]OperatorAtomHash = undefined;
    var written: usize = 0;
    for (presentation.modes) |mode| {
        if (isNeutralBosonicMode(presentation, mode)) try appendOperatorMode(mode, &mode_storage, &mode_atoms_storage, &mode_hash_storage, &written);
    }
    const neutral_count = written;
    for (presentation.modes) |mode| {
        if (isPlannedChargedFermion(presentation, mode, plan)) try appendOperatorMode(mode, &mode_storage, &mode_atoms_storage, &mode_hash_storage, &written);
    }
    const neutral_modes = mode_storage[0..neutral_count];
    const neutral_atoms = mode_atoms_storage[0..neutral_count];
    const neutral_hashes = mode_hash_storage[0..neutral_count];
    const charged_modes = mode_storage[neutral_count..written];
    const charged_atoms = mode_atoms_storage[neutral_count..written];
    const charged_hashes = mode_hash_storage[neutral_count..written];
    var charged_heads: [operator_join_max_level + 1]i32 = undefined;
    var charged_next: [operator_join_max_charged_fragments]i32 = undefined;
    var charged_fragments: [operator_join_max_charged_fragments]ChargedFragment = undefined;

    for (presentation.seeds) |seed| {
        const seed_budget = seedLevelBudget(query, seed) orelse continue;
        const base_count = try appendSeedRecordAtoms(seed, context.atoms);
        const max_descendants = @min(@as(usize, query.max_word_length), context.atoms.len - base_count);
        const needed_charged_count = neededChargedCount(seedCharge(seed, plan.charge_slot), target_charge, plan.charged_delta) orelse continue;
        const target_quantum_values = try writeTargetQuantumValues(presentation, query, plan, seed, basis_context);
        const charged_fragment_count = try buildChargedFragmentBuckets(
            charged_modes,
            needed_charged_count,
            seed_budget,
            &charged_heads,
            &charged_next,
            &charged_fragments,
        );
        const structural_hash = operatorRecordHashPrefix(
            presentation.id,
            seed,
            target_weight,
            seed_budget,
            target_quantum_values,
            context.atoms[0..base_count],
        );
        try emitNeutralChargedJoin(
            presentation,
            seed,
            base_count,
            target_weight,
            seed_budget,
            target_quantum_values,
            neutral_modes,
            neutral_atoms,
            neutral_hashes,
            charged_atoms,
            charged_hashes,
            0,
            0,
            base_count,
            max_descendants,
            structural_hash,
            charged_heads[0 .. seed_budget + 1],
            charged_next[0..charged_fragment_count],
            charged_fragments[0..charged_fragment_count],
            context,
            sink,
        );
    }
}

const TwoComponentNeutralChargedSplit = struct {
    left_component: u16,
    right_component: u16,
    plan: NeutralChargedPlan,
};

fn twoComponentNeutralChargedSplit(presentation: Presentation, query: Query) ?TwoComponentNeutralChargedSplit {
    const charge_slot = singleAdditiveExactQuerySlot(presentation, query) orelse return null;
    const left_component: u16 = if (query.level_match) |filter| filter.left_component else 0;
    const right_component: u16 = if (query.level_match) |filter| filter.right_component else 1;
    if (left_component == right_component) return null;

    var left_neutral_count: usize = 0;
    var left_charged_count: usize = 0;
    var right_neutral_count: usize = 0;
    var right_charged_count: usize = 0;
    var charged_delta: ?i32 = null;
    for (presentation.modes) |mode| {
        if (mode.component == left_component and isNeutralBosonicMode(presentation, mode)) {
            left_neutral_count += 1;
        } else if (mode.component == left_component) {
            const delta = chargedFermionDelta(presentation, mode, charge_slot) orelse return null;
            if (charged_delta) |existing| {
                if (existing != delta) return null;
            } else {
                charged_delta = delta;
            }
            left_charged_count += 1;
        } else if (mode.component == right_component and isNeutralBosonicMode(presentation, mode)) {
            right_neutral_count += 1;
        } else if (mode.component == right_component) {
            const delta = chargedFermionDelta(presentation, mode, charge_slot) orelse return null;
            if (charged_delta) |existing| {
                if (existing != delta) return null;
            } else {
                charged_delta = delta;
            }
            right_charged_count += 1;
        } else {
            return null;
        }
    }
    if (left_neutral_count == 0 or left_charged_count == 0 or right_neutral_count == 0 or right_charged_count == 0) return null;
    const delta = charged_delta orelse return null;

    for (presentation.seeds) |seed| {
        const seed_budget = seedLevelBudget(query, seed) orelse continue;
        if (seed_budget > operator_join_max_level) return null;
        const count = neededChargedCount(seedCharge(seed, charge_slot), query.quantum_filters[0].value, delta) orelse continue;
        if (count > 4) return null;
    }

    return .{
        .left_component = left_component,
        .right_component = right_component,
        .plan = .{ .charge_slot = charge_slot, .charged_delta = delta },
    };
}

fn seedComponentWeight(seed: Seed, component: usize) i32 {
    if (component < seed.component_weight_ticks.len) return seed.component_weight_ticks[component];
    return if (component == 0) seed.weight_ticks else 0;
}

fn emitClosedRecord(
    presentation: Presentation,
    seed: Seed,
    base_count: usize,
    total_weight_ticks: i32,
    level_ticks: u32,
    quantum_values: []const i32,
    left_component_weight: i32,
    right_component_weight: i32,
    depth: usize,
    structural_hash: u64,
    context: *OperatorContext,
    sink: anytype,
) !void {
    var component_weights = [_]i32{ left_component_weight, right_component_weight };
    try sink.emitOperatorRecord(OperatorRecord{
        .presentation = presentation.id,
        .seed = seed.id,
        .seed_body = seed.body,
        .base_atoms = context.atoms[0..base_count],
        .descendant_atoms = context.atoms[base_count..depth],
        .base_weight_ticks = seed.weight_ticks,
        .weight_ticks = total_weight_ticks,
        .level_ticks = level_ticks,
        .base_quantum_values = seed.quantum_values,
        .quantum_values = quantum_values,
        .base_component_weight_ticks = seed.component_weight_ticks,
        .component_weight_ticks = &component_weights,
        .structural_hash = structural_hash,
    });
}

fn emitRightChargedBucket(
    presentation: Presentation,
    seed: Seed,
    base_count: usize,
    total_weight_ticks: i32,
    seed_budget: u32,
    quantum_values: []const i32,
    left_component_weight: i32,
    right_component_weight: i32,
    charged_atoms: []const OperatorAtom,
    charged_hashes: []const OperatorAtomHash,
    remaining_level: u32,
    depth: usize,
    max_descendants: usize,
    structural_hash: u64,
    heads: []const i32,
    next: []const i32,
    fragments: []const ChargedFragment,
    context: *OperatorContext,
    sink: anytype,
) !void {
    var cursor = heads[remaining_level];
    while (cursor >= 0) {
        const fragment_index: usize = @intCast(cursor);
        const fragment = fragments[fragment_index];
        if (depth - base_count + fragment.count > max_descendants) {
            cursor = next[fragment_index];
            continue;
        }

        const appended = try appendChargedFragmentAtoms(fragment, charged_atoms, charged_hashes, context, depth, structural_hash);

        try emitClosedRecord(
            presentation,
            seed,
            base_count,
            total_weight_ticks,
            seed_budget,
            quantum_values,
            left_component_weight,
            right_component_weight,
            appended.depth,
            appended.hash,
            context,
            sink,
        );
        cursor = next[fragment_index];
    }
}

fn emitRightNeutralJoin(
    presentation: Presentation,
    seed: Seed,
    base_count: usize,
    total_weight_ticks: i32,
    seed_budget: u32,
    quantum_values: []const i32,
    left_component_weight: i32,
    right_component_weight: i32,
    neutral_modes: []const Mode,
    neutral_atoms: []const OperatorAtom,
    neutral_hashes: []const OperatorAtomHash,
    charged_atoms: []const OperatorAtom,
    charged_hashes: []const OperatorAtomHash,
    component_level: u32,
    neutral_level: u32,
    start_order: usize,
    depth: usize,
    max_descendants: usize,
    structural_hash: u64,
    heads: []const i32,
    next: []const i32,
    fragments: []const ChargedFragment,
    context: *OperatorContext,
    sink: anytype,
) !void {
    try emitRightChargedBucket(
        presentation,
        seed,
        base_count,
        total_weight_ticks,
        seed_budget,
        quantum_values,
        left_component_weight,
        right_component_weight,
        charged_atoms,
        charged_hashes,
        component_level - neutral_level,
        depth,
        max_descendants,
        structural_hash,
        heads,
        next,
        fragments,
        context,
        sink,
    );

    if (neutral_level >= component_level) return;
    if (depth - base_count >= max_descendants) return;

    var order = start_order;
    while (order < neutral_modes.len) : (order += 1) {
        const mode = neutral_modes[order];
        const next_level = neutral_level + mode.weight_ticks;
        if (next_level > component_level) continue;
        if (depth >= context.atoms.len) return Error.ContextTooSmall;
        context.atoms[depth] = neutral_atoms[order];
        const next_hash = appendOperatorAtomHash(structural_hash, neutral_hashes[order]);
        try emitRightNeutralJoin(
            presentation,
            seed,
            base_count,
            total_weight_ticks,
            seed_budget,
            quantum_values,
            left_component_weight,
            right_component_weight,
            neutral_modes,
            neutral_atoms,
            neutral_hashes,
            charged_atoms,
            charged_hashes,
            component_level,
            next_level,
            order,
            depth + 1,
            max_descendants,
            next_hash,
            heads,
            next,
            fragments,
            context,
            sink,
        );
    }
}

fn emitLeftChargedBucket(
    presentation: Presentation,
    seed: Seed,
    base_count: usize,
    total_weight_ticks: i32,
    seed_budget: u32,
    quantum_values: []const i32,
    left_component_weight: i32,
    right_component_weight: i32,
    right_neutral_modes: []const Mode,
    right_neutral_atoms: []const OperatorAtom,
    right_neutral_hashes: []const OperatorAtomHash,
    right_charged_atoms: []const OperatorAtom,
    right_charged_hashes: []const OperatorAtomHash,
    right_component_level: u32,
    left_charged_atoms: []const OperatorAtom,
    left_charged_hashes: []const OperatorAtomHash,
    remaining_level: u32,
    depth: usize,
    max_descendants: usize,
    structural_hash: u64,
    left_heads: []const i32,
    left_next: []const i32,
    left_fragments: []const ChargedFragment,
    right_heads: []const i32,
    right_next: []const i32,
    right_fragments: []const ChargedFragment,
    context: *OperatorContext,
    sink: anytype,
) !void {
    var cursor = left_heads[remaining_level];
    while (cursor >= 0) {
        const fragment_index: usize = @intCast(cursor);
        const fragment = left_fragments[fragment_index];
        if (depth - base_count + fragment.count > max_descendants) {
            cursor = left_next[fragment_index];
            continue;
        }

        const appended = try appendChargedFragmentAtoms(fragment, left_charged_atoms, left_charged_hashes, context, depth, structural_hash);

        try emitRightNeutralJoin(
            presentation,
            seed,
            base_count,
            total_weight_ticks,
            seed_budget,
            quantum_values,
            left_component_weight,
            right_component_weight,
            right_neutral_modes,
            right_neutral_atoms,
            right_neutral_hashes,
            right_charged_atoms,
            right_charged_hashes,
            right_component_level,
            0,
            0,
            appended.depth,
            max_descendants,
            appended.hash,
            right_heads,
            right_next,
            right_fragments,
            context,
            sink,
        );
        cursor = left_next[fragment_index];
    }
}

fn emitLeftNeutralJoin(
    presentation: Presentation,
    seed: Seed,
    base_count: usize,
    total_weight_ticks: i32,
    seed_budget: u32,
    quantum_values: []const i32,
    left_component_weight: i32,
    right_component_weight: i32,
    left_neutral_modes: []const Mode,
    left_neutral_atoms: []const OperatorAtom,
    left_neutral_hashes: []const OperatorAtomHash,
    left_charged_atoms: []const OperatorAtom,
    left_charged_hashes: []const OperatorAtomHash,
    left_component_level: u32,
    right_neutral_modes: []const Mode,
    right_neutral_atoms: []const OperatorAtom,
    right_neutral_hashes: []const OperatorAtomHash,
    right_charged_atoms: []const OperatorAtom,
    right_charged_hashes: []const OperatorAtomHash,
    right_component_level: u32,
    neutral_level: u32,
    start_order: usize,
    depth: usize,
    max_descendants: usize,
    structural_hash: u64,
    left_heads: []const i32,
    left_next: []const i32,
    left_fragments: []const ChargedFragment,
    right_heads: []const i32,
    right_next: []const i32,
    right_fragments: []const ChargedFragment,
    context: *OperatorContext,
    sink: anytype,
) !void {
    try emitLeftChargedBucket(
        presentation,
        seed,
        base_count,
        total_weight_ticks,
        seed_budget,
        quantum_values,
        left_component_weight,
        right_component_weight,
        right_neutral_modes,
        right_neutral_atoms,
        right_neutral_hashes,
        right_charged_atoms,
        right_charged_hashes,
        right_component_level,
        left_charged_atoms,
        left_charged_hashes,
        left_component_level - neutral_level,
        depth,
        max_descendants,
        structural_hash,
        left_heads,
        left_next,
        left_fragments,
        right_heads,
        right_next,
        right_fragments,
        context,
        sink,
    );

    if (neutral_level >= left_component_level) return;
    if (depth - base_count >= max_descendants) return;

    var order = start_order;
    while (order < left_neutral_modes.len) : (order += 1) {
        const mode = left_neutral_modes[order];
        const next_level = neutral_level + mode.weight_ticks;
        if (next_level > left_component_level) continue;
        if (depth >= context.atoms.len) return Error.ContextTooSmall;
        context.atoms[depth] = left_neutral_atoms[order];
        const next_hash = appendOperatorAtomHash(structural_hash, left_neutral_hashes[order]);
        try emitLeftNeutralJoin(
            presentation,
            seed,
            base_count,
            total_weight_ticks,
            seed_budget,
            quantum_values,
            left_component_weight,
            right_component_weight,
            left_neutral_modes,
            left_neutral_atoms,
            left_neutral_hashes,
            left_charged_atoms,
            left_charged_hashes,
            left_component_level,
            right_neutral_modes,
            right_neutral_atoms,
            right_neutral_hashes,
            right_charged_atoms,
            right_charged_hashes,
            right_component_level,
            next_level,
            order,
            depth + 1,
            max_descendants,
            next_hash,
            left_heads,
            left_next,
            left_fragments,
            right_heads,
            right_next,
            right_fragments,
            context,
            sink,
        );
    }
}

fn streamTwoComponentLevelMatchedOperatorJoin(presentation: Presentation, query: Query, split: TwoComponentNeutralChargedSplit, basis_context: *Context, context: *OperatorContext, sink: anytype) !void {
    const target_weight = switch (query.weight) {
        .exact => |ticks| ticks,
        .max => unreachable,
    };
    const target_charge = query.quantum_filters[0].value;
    if (presentation.modes.len > operator_join_max_modes) return Error.ContextTooSmall;

    var mode_storage: [operator_join_max_modes]Mode = undefined;
    var mode_atoms_storage: [operator_join_max_modes]OperatorAtom = undefined;
    var mode_hash_storage: [operator_join_max_modes]OperatorAtomHash = undefined;
    var written: usize = 0;
    for (presentation.modes) |mode| {
        if (mode.component == split.left_component and isNeutralBosonicMode(presentation, mode)) try appendOperatorMode(mode, &mode_storage, &mode_atoms_storage, &mode_hash_storage, &written);
    }
    const left_neutral_end = written;
    for (presentation.modes) |mode| {
        if (mode.component == split.left_component and isPlannedChargedFermion(presentation, mode, split.plan)) try appendOperatorMode(mode, &mode_storage, &mode_atoms_storage, &mode_hash_storage, &written);
    }
    const right_start = written;
    for (presentation.modes) |mode| {
        if (mode.component == split.right_component and isNeutralBosonicMode(presentation, mode)) try appendOperatorMode(mode, &mode_storage, &mode_atoms_storage, &mode_hash_storage, &written);
    }
    const right_neutral_end = written;
    for (presentation.modes) |mode| {
        if (mode.component == split.right_component and isPlannedChargedFermion(presentation, mode, split.plan)) try appendOperatorMode(mode, &mode_storage, &mode_atoms_storage, &mode_hash_storage, &written);
    }

    const left_neutral_modes = mode_storage[0..left_neutral_end];
    const left_charged_modes = mode_storage[left_neutral_end..right_start];
    const right_neutral_modes = mode_storage[right_start..right_neutral_end];
    const right_charged_modes = mode_storage[right_neutral_end..written];
    const left_neutral_atoms = mode_atoms_storage[0..left_neutral_end];
    const left_charged_atoms = mode_atoms_storage[left_neutral_end..right_start];
    const right_neutral_atoms = mode_atoms_storage[right_start..right_neutral_end];
    const right_charged_atoms = mode_atoms_storage[right_neutral_end..written];
    const left_neutral_hashes = mode_hash_storage[0..left_neutral_end];
    const left_charged_hashes = mode_hash_storage[left_neutral_end..right_start];
    const right_neutral_hashes = mode_hash_storage[right_start..right_neutral_end];
    const right_charged_hashes = mode_hash_storage[right_neutral_end..written];

    var left_heads: [operator_join_max_level + 1]i32 = undefined;
    var right_heads: [operator_join_max_level + 1]i32 = undefined;
    var left_next: [operator_join_max_charged_fragments]i32 = undefined;
    var right_next: [operator_join_max_charged_fragments]i32 = undefined;
    var left_fragments: [operator_join_max_charged_fragments]ChargedFragment = undefined;
    var right_fragments: [operator_join_max_charged_fragments]ChargedFragment = undefined;

    for (presentation.seeds) |seed| {
        const seed_budget = seedLevelBudget(query, seed) orelse continue;
        if (seed_budget > operator_join_max_level) return Error.ContextTooSmall;
        const base_count = try appendSeedRecordAtoms(seed, context.atoms);
        const max_descendants = @min(@as(usize, query.max_word_length), context.atoms.len - base_count);
        const needed_charged_count = neededChargedCount(seedCharge(seed, split.plan.charge_slot), target_charge, split.plan.charged_delta) orelse continue;
        const target_quantum_values = try writeTargetQuantumValues(presentation, query, split.plan, seed, basis_context);

        const left_base = seedComponentWeight(seed, split.left_component);
        const right_base = seedComponentWeight(seed, split.right_component);
        const structural_hash = operatorRecordHashPrefix(
            presentation.id,
            seed,
            target_weight,
            seed_budget,
            target_quantum_values,
            context.atoms[0..base_count],
        );

        const numerator = @as(i32, @intCast(seed_budget)) + right_base - left_base;
        if (@mod(numerator, 2) != 0) continue;
        const left_level_i32 = @divTrunc(numerator, 2);
        const right_level_i32 = @as(i32, @intCast(seed_budget)) - left_level_i32;
        if (left_level_i32 < 0 or right_level_i32 < 0) continue;
        const left_level: u32 = @intCast(left_level_i32);
        const right_level: u32 = @intCast(right_level_i32);

        var left_charged_count: usize = 0;
        while (left_charged_count <= needed_charged_count) : (left_charged_count += 1) {
            const right_charged_count = needed_charged_count - left_charged_count;
            const left_fragment_count = try buildChargedFragmentBuckets(
                left_charged_modes,
                left_charged_count,
                seed_budget,
                &left_heads,
                &left_next,
                &left_fragments,
            );
            const right_fragment_count = try buildChargedFragmentBuckets(
                right_charged_modes,
                right_charged_count,
                seed_budget,
                &right_heads,
                &right_next,
                &right_fragments,
            );

            try emitLeftNeutralJoin(
                presentation,
                seed,
                base_count,
                target_weight,
                seed_budget,
                target_quantum_values,
                left_base + left_level_i32,
                right_base + right_level_i32,
                left_neutral_modes,
                left_neutral_atoms,
                left_neutral_hashes,
                left_charged_atoms,
                left_charged_hashes,
                left_level,
                right_neutral_modes,
                right_neutral_atoms,
                right_neutral_hashes,
                right_charged_atoms,
                right_charged_hashes,
                right_level,
                0,
                0,
                base_count,
                max_descendants,
                structural_hash,
                left_heads[0 .. seed_budget + 1],
                left_next[0..left_fragment_count],
                left_fragments[0..left_fragment_count],
                right_heads[0 .. seed_budget + 1],
                right_next[0..right_fragment_count],
                right_fragments[0..right_fragment_count],
                context,
                sink,
            );
        }
    }
}

fn streamTwoComponentAllSplitsOperatorJoin(presentation: Presentation, query: Query, split: TwoComponentNeutralChargedSplit, basis_context: *Context, context: *OperatorContext, sink: anytype) !void {
    const target_weight = switch (query.weight) {
        .exact => |ticks| ticks,
        .max => unreachable,
    };
    const target_charge = query.quantum_filters[0].value;
    if (presentation.modes.len > operator_join_max_modes) return Error.ContextTooSmall;

    var merged_modes: [operator_join_max_modes]Mode = undefined;
    var merged_atoms: [operator_join_max_modes]OperatorAtom = undefined;
    var merged_hashes: [operator_join_max_modes]OperatorAtomHash = undefined;
    var written: usize = 0;

    for (presentation.modes) |mode| {
        if ((mode.component == split.left_component or mode.component == split.right_component) and isNeutralBosonicMode(presentation, mode)) {
            try appendOperatorMode(mode, &merged_modes, &merged_atoms, &merged_hashes, &written);
        }
    }
    const neutral_count = written;
    for (presentation.modes) |mode| {
        if ((mode.component == split.left_component or mode.component == split.right_component) and isPlannedChargedFermion(presentation, mode, split.plan)) {
            try appendOperatorMode(mode, &merged_modes, &merged_atoms, &merged_hashes, &written);
        }
    }

    const neutral_modes = merged_modes[0..neutral_count];
    const neutral_atoms = merged_atoms[0..neutral_count];
    const neutral_hashes = merged_hashes[0..neutral_count];
    const charged_modes = merged_modes[neutral_count..written];
    const charged_atoms = merged_atoms[neutral_count..written];
    const charged_hashes = merged_hashes[neutral_count..written];
    var charged_heads: [operator_join_max_level + 1]i32 = undefined;
    var charged_next: [operator_join_max_charged_fragments]i32 = undefined;
    var charged_fragments: [operator_join_max_charged_fragments]ChargedFragment = undefined;

    for (presentation.seeds) |seed| {
        const seed_budget = seedLevelBudget(query, seed) orelse continue;
        if (seed_budget > operator_join_max_level) return Error.ContextTooSmall;
        const base_count = try appendSeedRecordAtoms(seed, context.atoms);
        const max_descendants = @min(@as(usize, query.max_word_length), context.atoms.len - base_count);
        const needed_charged_count = neededChargedCount(seedCharge(seed, split.plan.charge_slot), target_charge, split.plan.charged_delta) orelse continue;
        const target_quantum_values = try writeTargetQuantumValues(presentation, query, split.plan, seed, basis_context);
        const charged_fragment_count = try buildChargedFragmentBuckets(
            charged_modes,
            needed_charged_count,
            seed_budget,
            &charged_heads,
            &charged_next,
            &charged_fragments,
        );
        const structural_hash = operatorRecordHashPrefix(
            presentation.id,
            seed,
            target_weight,
            seed_budget,
            target_quantum_values,
            context.atoms[0..base_count],
        );
        try emitNeutralChargedJoin(
            presentation,
            seed,
            base_count,
            target_weight,
            seed_budget,
            target_quantum_values,
            neutral_modes,
            neutral_atoms,
            neutral_hashes,
            charged_atoms,
            charged_hashes,
            0,
            0,
            base_count,
            max_descendants,
            structural_hash,
            charged_heads[0 .. seed_budget + 1],
            charged_next[0..charged_fragment_count],
            charged_fragments[0..charged_fragment_count],
            context,
            sink,
        );
    }
}

/// streamOperatorRecords streams structural operator records without rendering.
pub fn streamOperatorRecords(presentation: Presentation, query: Query, context: *Context, operator_context: *OperatorContext, sink: anytype) !void {
    if (canStreamBosonicOperatorOccupations(presentation, query)) {
        return streamBosonicOperatorOccupations(presentation, query, operator_context, sink);
    }
    if (twoComponentNeutralChargedSplit(presentation, query)) |split| {
        if (query.level_match == null) {
            return streamTwoComponentAllSplitsOperatorJoin(presentation, query, split, context, operator_context, sink);
        }
        return streamTwoComponentLevelMatchedOperatorJoin(presentation, query, split, context, operator_context, sink);
    }
    if (neutralChargedPlan(presentation, query)) |plan| {
        return streamNeutralChargedOperatorJoin(presentation, query, plan, context, operator_context, sink);
    }
    return streamGenericOperatorRecords(presentation, query, context, operator_context, sink);
}

const CountingSink = struct {
    count: usize = 0,
    max_depth: usize = 0,
    mixed_component_count: usize = 0,
    last_hash: u64 = 0,

    pub fn emitBasisState(self: *@This(), candidate: Candidate) !void {
        self.count += 1;
        self.max_depth = @max(self.max_depth, candidate.modes.len);
        self.last_hash = candidate.structuralHash();
        var saw_zero = false;
        var saw_one = false;
        for (candidate.modes) |mode| {
            saw_zero = saw_zero or mode.component == 0;
            saw_one = saw_one or mode.component == 1;
        }
        if (saw_zero and saw_one) self.mixed_component_count += 1;
    }
};

const OperatorCountingSink = struct {
    count: usize = 0,
    max_atoms: usize = 0,
    hash_mix: u64 = 0,
    first_derivative: u16 = 0,
    first_label: u16 = 0,
    first_seed_field: u32 = 0,
    saw_label_one: bool = false,

    pub fn emitOperatorRecord(self: *@This(), record: OperatorRecord) !void {
        self.count += 1;
        self.max_atoms = @max(self.max_atoms, record.base_atoms.len + record.descendant_atoms.len);
        self.hash_mix ^= record.structuralHash();
        for (record.base_atoms) |atom| {
            if (self.first_seed_field == 0) self.first_seed_field = atom.field;
        }
        for (record.descendant_atoms) |atom| {
            if (self.first_derivative == 0) {
                self.first_derivative = atom.derivative;
                self.first_label = atom.label;
            }
            self.saw_label_one = self.saw_label_one or atom.label == 1;
        }
    }
};

const TestTextWriter = struct {
    bytes: *std.ArrayList(u8),
    allocator: std.mem.Allocator,

    pub fn writeAll(self: *@This(), data: []const u8) !void {
        try self.bytes.appendSlice(self.allocator, data);
    }
};

test "additive reachability keeps prefixes repairable by later modes" {
    const testing = std.testing;
    const schema = [_]Quantum{.{ .kind = .additive }};
    const c_then_b = [_]Mode{
        .{ .id = 1, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{1} },
        .{ .id = 2, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{-1} },
    };
    const presentation = Presentation{ .quantum_schema = &schema, .modes = &c_then_b };
    const query = Query{ .weight = .{ .exact = 2 }, .quantum_filters = &.{.{ .slot = 0, .value = 0 }}, .max_word_length = 2 };
    var storage = StackContext(c_then_b.len, 2, schema.len, 2){};
    var context = storage.context();
    var sink = CountingSink{};

    try stream(presentation, query, &context, &sink);

    try testing.expectEqual(@as(usize, 1), sink.count);
    try testing.expectEqual(@as(usize, 2), sink.max_depth);
}

test "fermionic modes cannot repeat while bosonic modes can" {
    const testing = std.testing;
    const schema = [_]Quantum{};
    const fermion_mode = [_]Mode{.{ .id = 1, .weight_ticks = 1, .statistics = .fermionic }};
    const boson_mode = [_]Mode{.{ .id = 2, .weight_ticks = 1, .statistics = .bosonic }};
    const query = Query{ .weight = .{ .exact = 2 }, .max_word_length = 2 };

    var fermion_storage = StackContext(fermion_mode.len, 2, schema.len, 2){};
    var fermion_context = fermion_storage.context();
    var fermion_sink = CountingSink{};
    try stream(.{ .quantum_schema = &schema, .modes = &fermion_mode }, query, &fermion_context, &fermion_sink);
    try testing.expectEqual(@as(usize, 0), fermion_sink.count);

    var boson_storage = StackContext(boson_mode.len, 2, schema.len, 2){};
    var boson_context = boson_storage.context();
    var boson_sink = CountingSink{};
    try stream(.{ .quantum_schema = &schema, .modes = &boson_mode }, query, &boson_context, &boson_sink);
    try testing.expectEqual(@as(usize, 1), boson_sink.count);
}

test "product presentations stream merged component modes" {
    const testing = std.testing;
    const schema = [_]Quantum{.{ .kind = .additive }};
    const product_modes = [_]Mode{
        .{ .id = 1, .component = 0, .weight_ticks = 1, .statistics = .bosonic, .quantum_delta = &.{0} },
        .{ .id = 2, .component = 1, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{1} },
        .{ .id = 3, .component = 1, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{-1} },
    };
    const query = Query{ .weight = .{ .exact = 3 }, .quantum_filters = &.{.{ .slot = 0, .value = 0 }}, .max_word_length = 3 };
    var storage = StackContext(product_modes.len, 3, schema.len, 3){};
    var context = storage.context();
    var sink = CountingSink{};

    try stream(.{ .quantum_schema = &schema, .modes = &product_modes }, query, &context, &sink);

    try testing.expect(sink.count >= 1);
    try testing.expect(sink.mixed_component_count >= 1);
}

test "level matching filters product component weights" {
    const testing = std.testing;
    const modes = [_]Mode{
        .{ .id = 1, .component = 0, .weight_ticks = 1, .statistics = .bosonic },
        .{ .id = 2, .component = 1, .weight_ticks = 1, .statistics = .bosonic },
    };
    var storage = StackContextWithComponents(modes.len, 2, 0, 2, 2){};
    var context = storage.context();
    var sink = CountingSink{};
    try stream(.{ .modes = &modes }, .{
        .weight = .{ .exact = 2 },
        .level_match = .{},
        .max_word_length = 2,
    }, &context, &sink);
    try testing.expectEqual(@as(usize, 1), sink.count);
    try testing.expectEqual(@as(usize, 1), sink.mixed_component_count);
}

test "basis text sink writes state mode form" {
    const testing = std.testing;
    const modes = [_]Mode{.{ .id = 7, .weight_ticks = 1, .statistics = .bosonic }};
    const atoms = [_]RenderAtom{.{ .id = 7, .name = "X" }};
    var storage = StackContext(modes.len, 2, 0, 2){};
    var context = storage.context();
    var text: std.ArrayList(u8) = .empty;
    defer text.deinit(testing.allocator);
    var writer = TestTextWriter{ .bytes = &text, .allocator = testing.allocator };
    var sink = textSink(&writer, .{ .format = .state }, .{ .modes = &atoms });

    try stream(.{ .modes = &modes }, .{ .weight = .{ .exact = 2 }, .max_word_length = 2 }, &context, &sink);

    try testing.expect(std.mem.indexOf(u8, text.items, "|dX[0]_-1; dX[0]_-1>") != null);
}

test "basis text sink writes operator form at zero" {
    const testing = std.testing;
    const seed_quantum = [_]i32{1};
    const seeds = [_]Seed{.{ .id = 1, .weight_ticks = -1, .quantum_values = &seed_quantum, .body = 1 }};
    const modes = [_]Mode{.{ .id = 3, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{-1} }};
    const mode_atoms = [_]RenderAtom{.{ .id = 3, .name = "c", .base_weight_ticks = -1, .show_label = false }};
    const seed_atoms = [_]RenderAtom{.{ .id = 0, .name = "c", .base_weight_ticks = -1, .fixed_weight_ticks = -1, .show_label = false }};
    var storage = StackContext(modes.len, 1, 1, 1){};
    var context = storage.context();
    var text: std.ArrayList(u8) = .empty;
    defer text.deinit(testing.allocator);
    var writer = TestTextWriter{ .bytes = &text, .allocator = testing.allocator };
    var sink = textSink(&writer, .{ .format = .operator_at_zero }, .{ .modes = &mode_atoms, .seed_bits = &seed_atoms });

    try stream(.{ .quantum_schema = &Preset.ghost_schema, .modes = &modes, .seeds = &seeds }, .{
        .weight = .{ .exact = 0 },
        .quantum_filters = &.{.{ .slot = 0, .value = 0 }},
        .max_word_length = 1,
    }, &context, &sink);

    try testing.expect(std.mem.indexOf(u8, text.items, ":c(0) d^2c(0):") != null);
}

test "compact text sink exposes weighted charged base contribution" {
    const testing = std.testing;
    const seed_quantum = [_]i32{1};
    const seeds = [_]Seed{.{ .id = 1, .weight_ticks = -1, .quantum_values = &seed_quantum }};
    const modes = [_]Mode{.{ .id = 2, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{-1} }};
    var storage = StackContext(modes.len, 1, 1, 1){};
    var context = storage.context();
    var text: std.ArrayList(u8) = .empty;
    defer text.deinit(testing.allocator);
    var writer = TestTextWriter{ .bytes = &text, .allocator = testing.allocator };
    var sink = textSink(&writer, .{ .format = .compact }, .{});

    try stream(.{ .quantum_schema = &Preset.ghost_schema, .modes = &modes, .seeds = &seeds }, .{
        .weight = .{ .exact = 0 },
        .quantum_filters = &.{.{ .slot = 0, .value = 0 }},
        .max_word_length = 1,
    }, &context, &sink);

    try testing.expect(std.mem.indexOf(u8, text.items, "base_w=-1 w=0 l=1 base_q=[1] q=[0]") != null);
}

test "named quantum filters cover U1 ZN and fermion number" {
    const testing = std.testing;
    const schema = [_]Quantum{
        Preset.u1Charge("charge"),
        Preset.zn("phase", 3),
        Preset.zn("fermion-number", 2),
    };
    const modes = [_]Mode{
        .{ .id = 1, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{ 1, 1, 1 } },
        .{ .id = 2, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{ 1, 2, 1 } },
        .{ .id = 3, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{ -1, 0, 1 } },
    };
    const filters = [_]QuantumFilter{
        try quantumFilter(&schema, "charge", 0),
        try quantumFilter(&schema, "phase", 1),
        try quantumFilter(&schema, "fermion-number", 0),
    };
    var storage = StackContext(modes.len, 2, schema.len, 2){};
    var context = storage.context();
    var sink = CountingSink{};

    try stream(.{ .quantum_schema = &schema, .modes = &modes }, .{
        .weight = .{ .exact = 2 },
        .quantum_filters = &filters,
        .max_word_length = 2,
    }, &context, &sink);

    try testing.expectEqual(@as(usize, 1), sink.count);
    try testing.expectError(Error.UnknownQuantum, quantumFilter(&schema, "ghost-number", 0));
}

test "tensor representation placeholders reject filters explicitly" {
    const testing = std.testing;
    const schema = [_]Quantum{Preset.tensorRepresentation("so10-rep", 10)};
    const filters = [_]QuantumFilter{try quantumFilter(&schema, "so10-rep", 1)};
    const modes = [_]Mode{.{ .id = 1, .weight_ticks = 1, .statistics = .bosonic }};
    var storage = StackContext(modes.len, 1, schema.len, 1){};
    var context = storage.context();
    var sink = CountingSink{};

    try testing.expectError(Error.UnsupportedQuantumFilter, stream(.{ .quantum_schema = &schema, .modes = &modes }, .{
        .weight = .{ .exact = 1 },
        .quantum_filters = &filters,
        .max_word_length = 1,
    }, &context, &sink));
}

test "finite ZN quantum filters use suffix bitsets" {
    const testing = std.testing;
    const schema = [_]Quantum{.{ .kind = .zn, .modulus = 2 }};
    const modes = [_]Mode{
        .{ .id = 1, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{1} },
        .{ .id = 2, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{1} },
    };
    const query = Query{ .weight = .{ .exact = 2 }, .quantum_filters = &.{.{ .slot = 0, .value = 0 }}, .max_word_length = 2 };
    var storage = StackContext(modes.len, 2, schema.len, 2){};
    var context = storage.context();
    var sink = CountingSink{};

    try stream(.{ .quantum_schema = &schema, .modes = &modes }, query, &context, &sink);

    try testing.expectEqual(@as(usize, 1), sink.count);
}

test "oscillator families lower free boson bands without allocation" {
    const testing = std.testing;
    const schema = [_]Quantum{};
    const families = [_]OscillatorFamily{.{ .id = 1, .statistics = .bosonic, .first_tick = 1, .step_tick = 1 }};
    var modes_storage: [2]Mode = undefined;
    const modes = try buildOscillatorModes(&families, 2, &modes_storage);
    const query = Query{ .weight = .{ .exact = 2 }, .max_word_length = 2 };
    var storage = StackContext(2, 2, schema.len, 2){};
    var context = storage.context();
    var sink = CountingSink{};

    try stream(.{ .quantum_schema = &schema, .modes = modes }, query, &context, &sink);

    try testing.expectEqual(@as(usize, 2), modes.len);
    try testing.expectEqual(@as(usize, 2), sink.count);
}

test "oscillator multiplicity represents finite target labels" {
    const testing = std.testing;
    const schema = [_]Quantum{.{ .kind = .zn, .modulus = 2 }};
    const families = [_]OscillatorFamily{.{ .id = 1, .statistics = .fermionic, .first_tick = 1, .step_tick = 2, .multiplicity = 2, .quantum_delta = &.{1} }};
    var modes_storage: [2]Mode = undefined;
    const modes = try buildOscillatorModes(&families, 1, &modes_storage);
    const query = Query{ .weight = .{ .exact = 2 }, .quantum_filters = &.{.{ .slot = 0, .value = 0 }}, .max_word_length = 2 };
    var storage = StackContext(2, 2, schema.len, 2){};
    var context = storage.context();
    var sink = CountingSink{};

    try stream(.{ .quantum_schema = &schema, .modes = modes }, query, &context, &sink);

    try testing.expectEqual(@as(usize, 2), modes.len);
    try testing.expectEqual(@as(usize, 1), sink.count);
}

test "operator records stream bosonic occupations directly" {
    const testing = std.testing;
    const families = [_]OscillatorFamily{Preset.freeBosonFamily(1, 0, 2)};
    var modes_storage: [4]Mode = undefined;
    const modes = try buildOscillatorModes(&families, 2, &modes_storage);
    const query = Query{ .weight = .{ .exact = 2 }, .max_word_length = 2 };

    var compact_storage = StackContext(4, 2, 0, 2){};
    var compact_context = compact_storage.context();
    var compact_sink = CountingSink{};
    try stream(.{ .modes = modes }, query, &compact_context, &compact_sink);

    var fallback_storage = StackContext(4, 2, 0, 2){};
    var fallback_context = fallback_storage.context();
    var operator_storage = StackOperatorContext(2){};
    var operator_context = operator_storage.context();
    var operator_sink = OperatorCountingSink{};
    try streamOperatorRecords(.{ .modes = modes }, query, &fallback_context, &operator_context, &operator_sink);

    try testing.expectEqual(compact_sink.count, operator_sink.count);
    try testing.expectEqual(compact_sink.max_depth, operator_sink.max_atoms);
    try testing.expect(operator_sink.hash_mix != 0);
    try testing.expect(operator_sink.saw_label_one);
}

test "operator fallback lowers compact bc derivatives without printing" {
    const testing = std.testing;
    const seed_quantum = [_]i32{1};
    const seeds = [_]Seed{.{ .id = 1, .weight_ticks = -1, .quantum_values = &seed_quantum, .body = 1 }};
    const modes = [_]Mode{.{
        .id = 3,
        .weight_ticks = 1,
        .base_weight_ticks = -1,
        .statistics = .fermionic,
        .quantum_delta = &.{-1},
    }};
    var compact_storage = StackContext(modes.len, 1, 1, 1){};
    var compact_context = compact_storage.context();
    var operator_storage = StackOperatorContext(2){};
    var operator_context = operator_storage.context();
    var sink = OperatorCountingSink{};

    try streamOperatorRecords(.{ .quantum_schema = &Preset.ghost_schema, .modes = &modes, .seeds = &seeds }, .{
        .weight = .{ .exact = 0 },
        .quantum_filters = &.{.{ .slot = 0, .value = 0 }},
        .max_word_length = 1,
    }, &compact_context, &operator_context, &sink);

    try testing.expectEqual(@as(usize, 1), sink.count);
    try testing.expectEqual(@as(usize, 2), sink.max_atoms);
    try testing.expectEqual(@as(u16, 2), sink.first_derivative);
}

test "operator fast join is selected from descriptor structure not mode order" {
    const testing = std.testing;
    const schema = [_]Quantum{.{ .kind = .additive }};
    const seed_quantum = [_]i32{1};
    const seeds = [_]Seed{.{ .id = 1, .weight_ticks = 0, .quantum_values = &seed_quantum, .body = 1 }};
    const modes = [_]Mode{
        .{ .id = 2, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{-1} },
        .{ .id = 3, .weight_ticks = 1, .statistics = .bosonic, .quantum_delta = &.{0} },
        .{ .id = 4, .weight_ticks = 2, .statistics = .fermionic, .quantum_delta = &.{-1} },
        .{ .id = 5, .weight_ticks = 2, .statistics = .bosonic, .quantum_delta = &.{0} },
    };
    const query = Query{
        .weight = .{ .exact = 2 },
        .quantum_filters = &.{.{ .slot = 0, .value = 0 }},
        .max_word_length = 2,
    };

    var compact_storage = StackContext(modes.len, 2, schema.len, 2){};
    var compact_context = compact_storage.context();
    var compact_sink = CountingSink{};
    try stream(.{ .quantum_schema = &schema, .modes = &modes, .seeds = &seeds }, query, &compact_context, &compact_sink);

    var no_fallback_storage = StackContext(modes.len, 2, schema.len, 0){};
    var no_fallback_context = no_fallback_storage.context();
    var operator_storage = StackOperatorContext(3){};
    var operator_context = operator_storage.context();
    var operator_sink = OperatorCountingSink{};
    try streamOperatorRecords(.{ .quantum_schema = &schema, .modes = &modes, .seeds = &seeds }, query, &no_fallback_context, &operator_context, &operator_sink);

    try testing.expectEqual(compact_sink.count, operator_sink.count);
    try testing.expect(operator_sink.count != 0);
}

test "operator fast join infers charge slot and delta from descriptor" {
    const testing = std.testing;
    const schema = [_]Quantum{
        .{ .kind = .additive },
        .{ .kind = .additive },
    };
    const seed_quantum = [_]i32{ 7, -4 };
    const seeds = [_]Seed{primarySeed(.{ .id = 42, .quantum_values = &seed_quantum })};
    const modes = [_]Mode{
        .{ .id = 2, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{ 0, 2 } },
        .{ .id = 3, .weight_ticks = 1, .statistics = .bosonic, .quantum_delta = &.{ 0, 0 } },
    };
    const query = Query{
        .weight = .{ .exact = 2 },
        .quantum_filters = &.{.{ .slot = 1, .value = -2 }},
        .max_word_length = 2,
    };

    var compact_storage = StackContext(modes.len, 2, schema.len, 2){};
    var compact_context = compact_storage.context();
    var compact_sink = CountingSink{};
    try stream(.{ .quantum_schema = &schema, .modes = &modes, .seeds = &seeds }, query, &compact_context, &compact_sink);

    var no_fallback_storage = StackContext(modes.len, 2, schema.len, 0){};
    var no_fallback_context = no_fallback_storage.context();
    var operator_storage = StackOperatorContext(3){};
    var operator_context = operator_storage.context();
    var operator_sink = OperatorCountingSink{};
    try streamOperatorRecords(.{ .quantum_schema = &schema, .modes = &modes, .seeds = &seeds }, query, &no_fallback_context, &operator_context, &operator_sink);

    try testing.expectEqual(compact_sink.count, operator_sink.count);
    try testing.expectEqual(@as(usize, 1), operator_sink.count);
    try testing.expectEqual(@as(u32, 42), operator_sink.first_seed_field);
}

test "generic operator stream supports arbitrary charged primary descriptors" {
    const testing = std.testing;
    const schema = [_]Quantum{
        .{ .kind = .additive },
        .{ .kind = .additive },
    };
    const seed_quantum = [_]i32{ 3, -2 };
    const seeds = [_]Seed{primarySeed(.{
        .id = 42,
        .weight_ticks = 1,
        .quantum_values = &seed_quantum,
    })};
    const modes = [_]Mode{
        .{ .id = 10, .weight_ticks = 1, .statistics = .bosonic, .quantum_delta = &.{ 0, 0 } },
        .{ .id = 11, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{ -1, 2 } },
    };
    const query = Query{
        .weight = .{ .exact = 3 },
        .quantum_filters = &.{
            .{ .slot = 0, .value = 2 },
            .{ .slot = 1, .value = 0 },
        },
        .max_word_length = 2,
    };

    var compact_storage = StackContext(modes.len, 2, schema.len, 2){};
    var compact_context = compact_storage.context();
    var compact_sink = CountingSink{};
    try stream(.{ .quantum_schema = &schema, .modes = &modes, .seeds = &seeds }, query, &compact_context, &compact_sink);

    var no_fallback_storage = StackContext(modes.len, 2, schema.len, 0){};
    var no_fallback_context = no_fallback_storage.context();
    var operator_storage = StackOperatorContext(3){};
    var operator_context = operator_storage.context();
    var operator_sink = OperatorCountingSink{};
    try streamOperatorRecords(.{ .quantum_schema = &schema, .modes = &modes, .seeds = &seeds }, query, &no_fallback_context, &operator_context, &operator_sink);

    try testing.expectEqual(compact_sink.count, operator_sink.count);
    try testing.expectEqual(@as(usize, 1), operator_sink.count);
    try testing.expectEqual(@as(u32, 42), operator_sink.first_seed_field);
}

test "signed seed weights support ghost primary weights" {
    const testing = std.testing;
    const schema = [_]Quantum{.{ .kind = .additive }};
    const seeds = [_]Seed{.{ .id = 1, .weight_ticks = -1, .quantum_values = &.{1} }};
    const modes = [_]Mode{.{ .id = 2, .weight_ticks = 1, .statistics = .fermionic, .quantum_delta = &.{-1} }};
    const query = Query{ .weight = .{ .exact = 0 }, .quantum_filters = &.{.{ .slot = 0, .value = 0 }}, .max_word_length = 1 };
    var storage = StackContext(modes.len, 1, schema.len, 1){};
    var context = storage.context();
    var sink = CountingSink{};

    try stream(.{ .quantum_schema = &schema, .modes = &modes, .seeds = &seeds }, query, &context, &sink);

    try testing.expectEqual(@as(usize, 1), sink.count);
}

test "bc preset descriptors match low-weight prototype ghost counts" {
    const testing = std.testing;
    const seed_families = [_]SeedFamily{Preset.bcSeedFamily(1, 0)};
    var seed_options_storage: [2]SeedOption = undefined;
    const seed_options = try buildSeedOptions(&seed_families, &seed_options_storage);
    var seeds_storage: [4]Seed = undefined;
    var seed_quantum_storage: [4]i32 = undefined;
    const seeds = try buildFermionicSeedSubsets(seed_options, Preset.ghost_schema.len, &seeds_storage, &seed_quantum_storage);

    const mode_families = Preset.bcOscillatorFamilies(2, 3, 0);
    var mode_storage: [5]Mode = undefined;
    const modes = try buildOscillatorModes(&mode_families, 3, &mode_storage);

    var max_zero_storage = StackContext(5, 1, Preset.ghost_schema.len, 0){};
    var max_zero_context = max_zero_storage.context();
    var max_zero_sink = CountingSink{};
    try stream(.{ .quantum_schema = &Preset.ghost_schema, .modes = modes, .seeds = seeds }, .{
        .weight = .{ .max = 0 },
        .quantum_filters = &.{.{ .slot = 0, .value = 1 }},
        .max_word_length = 0,
    }, &max_zero_context, &max_zero_sink);

    var exact_two_storage = StackContext(5, 3, Preset.ghost_schema.len, 1){};
    var exact_two_context = exact_two_storage.context();
    var exact_two_sink = CountingSink{};
    try stream(.{ .quantum_schema = &Preset.ghost_schema, .modes = modes, .seeds = seeds }, .{
        .weight = .{ .exact = 2 },
        .quantum_filters = &.{.{ .slot = 0, .value = -1 }},
        .max_word_length = 1,
    }, &exact_two_context, &exact_two_sink);

    try testing.expectEqual(@as(usize, 2), max_zero_sink.count);
    try testing.expectEqual(@as(usize, 2), exact_two_sink.count);
}

test "eta-xi preset descriptors expose xi zero seed and positive jets" {
    const testing = std.testing;
    const seed_families = [_]SeedFamily{Preset.etaXiSeedFamily(1, 0)};
    var seed_options_storage: [1]SeedOption = undefined;
    const seed_options = try buildSeedOptions(&seed_families, &seed_options_storage);
    var seeds_storage: [2]Seed = undefined;
    var seed_quantum_storage: [2]i32 = undefined;
    const seeds = try buildFermionicSeedSubsets(seed_options, Preset.eta_xi_schema.len, &seeds_storage, &seed_quantum_storage);

    const mode_families = Preset.etaXiOscillatorFamilies(2, 3, 0);
    var mode_storage: [2]Mode = undefined;
    const modes = try buildOscillatorModes(&mode_families, 1, &mode_storage);
    var storage = StackContext(2, 1, Preset.eta_xi_schema.len, 0){};
    var context = storage.context();
    var sink = CountingSink{};

    try stream(.{ .quantum_schema = &Preset.eta_xi_schema, .modes = modes, .seeds = seeds }, .{
        .weight = .{ .exact = 0 },
        .quantum_filters = &.{try quantumFilter(&Preset.eta_xi_schema, "eta-xi-number", -1)},
        .max_word_length = 0,
    }, &context, &sink);

    try testing.expectEqual(@as(usize, 2), modes.len);
    try testing.expectEqual(@as(usize, 1), sink.count);
}

fn minDistinctModeSum(count: usize) i32 {
    if (count == 0) return 0;
    return @intCast((count * (count - 1)) / 2);
}

fn distinctModeSumCount(count: usize, sum: i32, first: usize) usize {
    if (count == 0) return if (sum == 0) 1 else 0;
    if (sum < minDistinctModeSum(count)) return 0;

    var total: usize = 0;
    var value = first;
    while (value <= @as(usize, @intCast(sum))) : (value += 1) {
        total += distinctModeSumCount(count - 1, sum - @as(i32, @intCast(value)), value + 1);
    }
    return total;
}

fn bcExactCountPf(weight: i32, ghost: i32) usize {
    var total: usize = 0;
    const min_b_count: usize = if (ghost < 0) @intCast(-ghost) else 0;
    const abs_ghost: i32 = if (ghost < 0) -ghost else ghost;
    const max_b_count: usize = @intCast(weight + abs_ghost + 8);
    var b_count = min_b_count;
    while (b_count <= max_b_count) : (b_count += 1) {
        const c_count_i32 = ghost + @as(i32, @intCast(b_count));
        if (c_count_i32 < 0) continue;
        const c_count: usize = @intCast(c_count_i32);
        const min_b_sum = minDistinctModeSum(b_count);
        const min_c_sum = minDistinctModeSum(c_count);
        const max_b_sum = weight + ghost - @as(i32, @intCast(b_count)) - min_c_sum;
        if (max_b_sum < min_b_sum) continue;

        var b_sum = min_b_sum;
        while (b_sum <= max_b_sum) : (b_sum += 1) {
            const c_sum = weight + ghost - @as(i32, @intCast(b_count)) - b_sum;
            if (c_sum < min_c_sum) continue;
            total += distinctModeSumCount(b_count, b_sum, 0) * distinctModeSumCount(c_count, c_sum, 0);
        }
    }
    return total;
}

test "bc compact descriptor exposes first handoff slice" {
    const testing = std.testing;
    const seed_families = [_]SeedFamily{Preset.bcSeedFamily(1, 0)};
    var seed_options_storage: [2]SeedOption = undefined;
    const seed_options = try buildSeedOptions(&seed_families, &seed_options_storage);
    var seeds_storage: [4]Seed = undefined;
    var seed_quantum_storage: [4]i32 = undefined;
    const seeds = try buildFermionicSeedSubsets(seed_options, Preset.ghost_schema.len, &seeds_storage, &seed_quantum_storage);

    const mode_families = Preset.bcOscillatorFamilies(2, 3, 0);
    var mode_storage: [1]Mode = undefined;
    const modes = try buildOscillatorModes(&mode_families, 1, &mode_storage);
    var storage = StackContext(1, 1, Preset.ghost_schema.len, 1){};
    var context = storage.context();
    var sink = CountingSink{};

    try stream(.{ .quantum_schema = &Preset.ghost_schema, .modes = modes, .seeds = seeds[1..] }, .{
        .weight = .{ .exact = 0 },
        .quantum_filters = &.{.{ .slot = 0, .value = 0 }},
        .max_word_length = 1,
    }, &context, &sink);

    try testing.expectEqual(@as(usize, 1), sink.count);
    try testing.expectEqual(@as(usize, 1), sink.max_depth);
}
