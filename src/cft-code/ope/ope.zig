const std = @import("std");
const descriptor = @import("../correlators/descriptor.zig");
const generated_fixtures = @import("../correlators/generated_fixtures.zig");

/// BenchmarkDescriptors exposes generated descriptor fixtures for benchmark binaries.
pub const BenchmarkDescriptors = struct {
    /// bc is the generated holomorphic bc-ghost sphere descriptor.
    pub const bc = generated_fixtures.bc_descriptor;
    /// free_fermion is the generated 10D holomorphic free-fermion descriptor.
    pub const free_fermion = generated_fixtures.free_fermion_descriptor;
    /// free_boson is the generated 10D free-boson sphere descriptor.
    pub const free_boson = generated_fixtures.free_boson_descriptor;
};

/// Limits fixes all scratch capacities used by the generic OPE walker.
pub const Limits = struct {
    max_factors: usize = 16,
    max_output_factors: usize = 32,
    max_coordinates: usize = 32,
    max_tensors: usize = 32,
    max_actions: usize = 16,
    max_scalar_atoms: usize = 8,
    max_taylor_level: u8 = 0,
};

/// PrimitiveFactor is one descriptor field with a derivative order and compact labels.
pub const PrimitiveFactor = struct {
    field: descriptor.Id,
    derivative: u8 = 0,
    labels: []const u32 = &.{},
};

/// Monomial is one normal-ordered primitive word with an exact scalar.
pub const Monomial = struct {
    scalar: Scalar = .one,
    factors: []const PrimitiveFactor,
};

/// Expression is an expanded sum of monomials.
pub const Expression = struct {
    terms: []const Monomial,
};

/// Projection bounds the local Taylor expansion requested from the OPE.
pub const Projection = struct {
    target_holomorphic_ticks: i32 = 0,
    max_taylor_level: u8 = 0,
};

/// Scalar is a small exact coefficient with optional symbolic atom powers.
pub const Scalar = struct {
    pub const Atom = struct {
        symbol: descriptor.Id,
        power: i16,
    };

    numerator: i64 = 1,
    denominator: i64 = 1,
    imaginary_power: u2 = 0,
    atoms: [8]Atom = undefined,
    atom_count: u8 = 0,

    pub const one: Scalar = .{};

    fn normalize(self: *Scalar) void {
        if (self.numerator == 0) {
            self.denominator = 1;
            self.imaginary_power = 0;
            self.atom_count = 0;
            return;
        }
        if (self.denominator < 0) {
            self.numerator = -self.numerator;
            self.denominator = -self.denominator;
        }
        const divisor: i64 = @intCast(std.math.gcd(absInt(self.numerator), absInt(self.denominator)));
        self.numerator = @divExact(self.numerator, divisor);
        self.denominator = @divExact(self.denominator, divisor);
    }

    fn absInt(value: i64) u64 {
        if (value == std.math.minInt(i64)) return @as(u64, 1) << 63;
        return if (value < 0) @intCast(-value) else @intCast(value);
    }

    fn mulRational(self: *Scalar, numerator: i64, denominator: i64) !void {
        if (denominator == 0) return error.InvalidScalar;
        self.numerator = try std.math.mul(i64, self.numerator, numerator);
        self.denominator = try std.math.mul(i64, self.denominator, denominator);
        self.normalize();
    }

    fn add(self: *Scalar, rhs: Scalar) !void {
        if (self.imaginary_power != rhs.imaginary_power or self.atom_count != rhs.atom_count) return error.IncompatibleScalar;
        for (self.atoms[0..self.atom_count], rhs.atoms[0..rhs.atom_count]) |left, right| {
            if (left.symbol != right.symbol or left.power != right.power) return error.IncompatibleScalar;
        }
        const left_num = try std.math.mul(i64, self.numerator, rhs.denominator);
        const right_num = try std.math.mul(i64, rhs.numerator, self.denominator);
        self.numerator = try std.math.add(i64, left_num, right_num);
        self.denominator = try std.math.mul(i64, self.denominator, rhs.denominator);
        self.normalize();
    }

    fn mulImaginary(self: *Scalar, power: u2) void {
        self.imaginary_power +%= power;
    }

    fn mulAtom(self: *Scalar, comptime limits: Limits, symbol: descriptor.Id, power: i16) !void {
        if (power == 0) return;
        for (self.atoms[0..self.atom_count]) |*atom| {
            if (atom.symbol == symbol) {
                atom.power += power;
                return;
            }
        }
        if (self.atom_count >= @min(limits.max_scalar_atoms, self.atoms.len)) return error.ContextTooSmall;
        self.atoms[self.atom_count] = .{ .symbol = symbol, .power = power };
        self.atom_count += 1;
    }

    fn mulMonomial(self: *Scalar, comptime limits: Limits, value: descriptor.ScalarMonomial) !void {
        try self.mulRational(value.rational.numerator, value.rational.denominator);
        self.mulImaginary(value.imaginary_power);
        if (value.atom) |symbol| try self.mulAtom(limits, symbol, value.atom_power);
    }

    fn mulFactor(self: *Scalar, comptime d: descriptor.Descriptor, comptime limits: Limits, factor: descriptor.ScalarFactor) !void {
        switch (factor) {
            .one => {},
            .rational => |value| try self.mulRational(value.numerator, value.denominator),
            .monomial => |value| try self.mulMonomial(limits, value),
            .parameter => |id| try self.mulAtom(limits, try parameterSymbol(d, id), 1),
            .neg_parameter_half => |id| {
                try self.mulRational(-1, 2);
                try self.mulAtom(limits, try parameterSymbol(d, id), 1);
            },
            .neg_i_parameter_half => |id| {
                try self.mulRational(-1, 2);
                self.mulImaginary(1);
                try self.mulAtom(limits, try parameterSymbol(d, id), 1);
            },
            .parameter_half => |id| {
                try self.mulRational(1, 2);
                try self.mulAtom(limits, try parameterSymbol(d, id), 1);
            },
        }
    }
};

fn parameterSymbol(comptime d: descriptor.Descriptor, id: descriptor.Id) !descriptor.Id {
    if (id >= d.parameters.len) return error.InvalidScalar;
    return d.parameters[id].symbol;
}

fn mergeDifferencePower(existing: *CoordinateAtom, candidate: CoordinateAtom) bool {
    if (std.meta.activeTag(existing.*) != .difference_power or std.meta.activeTag(candidate) != .difference_power) return false;
    const old = &existing.difference_power;
    const new = candidate.difference_power;
    if (old.left_slot != new.left_slot or old.right_slot != new.right_slot) return false;
    old.exponent += new.exponent;
    old.left_derivatives += new.left_derivatives;
    old.right_derivatives += new.right_derivatives;
    return true;
}

/// CoordinateAtom is one explicit local coordinate multiplier in an emitted term.
pub const CoordinateAtom = union(enum) {
    difference_power: struct {
        left_slot: descriptor.CoordinateSlot,
        right_slot: descriptor.CoordinateSlot,
        exponent: i16,
        left_derivatives: u8,
        right_derivatives: u8,
    },
    logarithm: struct {
        left_slot: descriptor.CoordinateSlot,
        right_slot: descriptor.CoordinateSlot,
        left_derivatives: u8,
        right_derivatives: u8,
    },
    named_kernel: struct {
        symbol: descriptor.Id,
        left_slot: descriptor.CoordinateSlot,
        right_slot: descriptor.CoordinateSlot,
        left_derivatives: u8,
        right_derivatives: u8,
    },
    green_exponential: struct {
        left_slot: descriptor.CoordinateSlot,
        right_slot: descriptor.CoordinateSlot,
    },
    local_power: struct {
        source_index: u8,
        power: u8,
    },
};

/// TensorAtom is one coefficient tensor with runtime labels resolved.
pub const TensorAtom = union(enum) {
    none,
    metric: struct { left: u32, right: u32 },
    momentum_index: struct { momentum: u32, index: u32 },
    momentum_pair: struct { left: u32, right: u32 },
};

/// ActionAtom is one residual action with runtime labels resolved.
pub const ActionAtom = union(enum) {
    profile_derivative: struct { profile: u32, index: u32 },
};

/// OutputFactor is one primitive derivative field in the explicit RHS operator.
pub const OutputFactor = PrimitiveFactor;

/// TermView is valid only during the sink call that receives it.
pub const TermView = struct {
    scalar: Scalar,
    coordinates: []const CoordinateAtom,
    tensors: []const TensorAtom,
    actions: []const ActionAtom,
    output: []const OutputFactor,
    branch_level: u8,
};

/// CountHashSink counts explicit terms and accumulates a deterministic structural hash.
pub const CountHashSink = struct {
    term_count: usize = 0,
    hash: u64 = 0,
    max_output_len: usize = 0,

    pub fn emitOpeTerm(self: *@This(), term: TermView) !void {
        self.term_count += 1;
        if (term.output.len > self.max_output_len) self.max_output_len = term.output.len;
        var h = std.hash.Wyhash.init(0x6f70655f70726f6a);
        hashScalar(&h, term.scalar);
        h.update(std.mem.asBytes(&term.branch_level));
        for (term.coordinates) |coordinate| hashCoordinate(&h, coordinate);
        for (term.tensors) |tensor| hashTensor(&h, tensor);
        for (term.actions) |action| hashAction(&h, action);
        for (term.output) |factor| hashFactor(&h, factor);
        self.hash +%= h.final();
    }

    fn hashScalar(h: *std.hash.Wyhash, scalar: Scalar) void {
        h.update(std.mem.asBytes(&scalar.numerator));
        h.update(std.mem.asBytes(&scalar.denominator));
        h.update(std.mem.asBytes(&scalar.imaginary_power));
        h.update(std.mem.asBytes(&scalar.atom_count));
        for (scalar.atoms[0..scalar.atom_count]) |atom| h.update(std.mem.asBytes(&atom));
    }

    fn hashCoordinate(h: *std.hash.Wyhash, coordinate: CoordinateAtom) void {
        const tag: u8 = @intFromEnum(coordinate);
        h.update(std.mem.asBytes(&tag));
        switch (coordinate) {
            inline else => |payload| h.update(std.mem.asBytes(&payload)),
        }
    }

    fn hashTensor(h: *std.hash.Wyhash, tensor: TensorAtom) void {
        const tag: u8 = @intFromEnum(tensor);
        h.update(std.mem.asBytes(&tag));
        switch (tensor) {
            inline else => |payload| h.update(std.mem.asBytes(&payload)),
        }
    }

    fn hashAction(h: *std.hash.Wyhash, action: ActionAtom) void {
        const tag: u8 = @intFromEnum(action);
        h.update(std.mem.asBytes(&tag));
        switch (action) {
            inline else => |payload| h.update(std.mem.asBytes(&payload)),
        }
    }

    fn hashFactor(h: *std.hash.Wyhash, factor: OutputFactor) void {
        h.update(std.mem.asBytes(&factor.field));
        h.update(std.mem.asBytes(&factor.derivative));
        for (factor.labels) |label| h.update(std.mem.asBytes(&label));
    }
};

/// FixedCollector combines equal structural terms in a caller-owned table.
pub fn FixedCollector(comptime capacity: usize) type {
    return struct {
        const Entry = struct {
            used: bool = false,
            structure_hash: u64 = 0,
            scalar: Scalar = .one,
        };

        entries: [capacity]Entry = [_]Entry{.{}} ** capacity,
        term_count: usize = 0,
        raw_term_count: usize = 0,
        hash: u64 = 0,

        pub fn emitOpeTerm(self: *@This(), term: TermView) !void {
            self.raw_term_count += 1;
            const structure_hash = termStructureHash(term);
            var index = structure_hash % capacity;
            var probes: usize = 0;
            while (probes < capacity) : (probes += 1) {
                const slot = &self.entries[index];
                if (!slot.used) {
                    slot.* = .{
                        .used = true,
                        .structure_hash = structure_hash,
                        .scalar = term.scalar,
                    };
                    self.term_count += 1;
                    return;
                }
                if (slot.structure_hash == structure_hash) {
                    try slot.scalar.add(term.scalar);
                    return;
                }
                index += 1;
                if (index == capacity) index = 0;
            }
            return error.ContextTooSmall;
        }

        pub fn finish(self: *@This()) void {
            self.hash = 0;
            self.term_count = 0;
            for (self.entries) |entry| {
                if (!entry.used or entry.scalar.numerator == 0) continue;
                self.term_count += 1;
                var h = std.hash.Wyhash.init(0x636f6c6c656374);
                CountHashSink.hashScalar(&h, entry.scalar);
                h.update(std.mem.asBytes(&entry.structure_hash));
                self.hash +%= h.final();
            }
        }
    };
}

fn termStructureHash(term: TermView) u64 {
    var h = std.hash.Wyhash.init(0x6f70655f73747275);
    h.update(std.mem.asBytes(&term.branch_level));
    for (term.coordinates) |coordinate| CountHashSink.hashCoordinate(&h, coordinate);
    for (term.tensors) |tensor| CountHashSink.hashTensor(&h, tensor);
    for (term.actions) |action| CountHashSink.hashAction(&h, action);
    for (term.output) |factor| CountHashSink.hashFactor(&h, factor);
    return h.final();
}

/// GenericKernel returns a descriptor-specialized explicit OPE walker.
pub fn GenericKernel(comptime d: descriptor.Descriptor, comptime limits: Limits) type {
    comptime {
        descriptor.validateDescriptor(d) catch |err| @compileError(@errorName(err));
    }
    return struct {
        const Self = @This();

        /// opeProjected streams the explicit projected OPE of two expanded inputs.
        pub fn opeProjected(left: Expression, right: Expression, projection: Projection, sink: anytype) !void {
            if (projection.max_taylor_level > limits.max_taylor_level) return error.ContextTooSmall;
            for (left.terms) |left_term| {
                for (right.terms) |right_term| {
                    try expandMonomialPair(left_term, right_term, projection, sink);
                }
            }
        }

        fn expandMonomialPair(left: Monomial, right: Monomial, projection: Projection, sink: anytype) !void {
            if (left.factors.len > limits.max_factors or right.factors.len > limits.max_factors) return error.ContextTooSmall;
            var state = Scratch{};
            state.scalar = left.scalar;
            try state.scalar.mulRational(right.scalar.numerator, right.scalar.denominator);
            state.scalar.mulImaginary(right.scalar.imaginary_power);
            for (right.scalar.atoms[0..right.scalar.atom_count]) |atom| try state.scalar.mulAtom(limits, atom.symbol, atom.power);
            const force_all_contracted = !survivorProjectionPossible(left, right, projection);
            try walk(left, right, projection, force_all_contracted, 0, &state, sink);
        }

        const Scratch = struct {
            contracted_left: [limits.max_factors]bool = [_]bool{false} ** limits.max_factors,
            contracted_right: [limits.max_factors]bool = [_]bool{false} ** limits.max_factors,
            scalar: Scalar = .one,
            coordinates: [limits.max_coordinates]CoordinateAtom = undefined,
            coordinate_count: usize = 0,
            tensors: [limits.max_tensors]TensorAtom = undefined,
            tensor_count: usize = 0,
            actions: [limits.max_actions]ActionAtom = undefined,
            action_count: usize = 0,
            output: [limits.max_output_factors]OutputFactor = undefined,
            output_count: usize = 0,
            branch_level: u8 = 0,

            fn addOutput(self: *Scratch, factor: OutputFactor) !void {
                if (self.output_count >= self.output.len) return error.ContextTooSmall;
                self.output[self.output_count] = factor;
                self.output_count += 1;
            }

            fn addCoordinate(self: *Scratch, coordinate: CoordinateAtom) !void {
                if (std.meta.activeTag(coordinate) == .difference_power) {
                    for (self.coordinates[0..self.coordinate_count]) |*existing| {
                        if (mergeDifferencePower(existing, coordinate)) return;
                    }
                }
                if (self.coordinate_count >= self.coordinates.len) return error.ContextTooSmall;
                self.coordinates[self.coordinate_count] = coordinate;
                self.coordinate_count += 1;
            }

            fn addTensor(self: *Scratch, tensor: TensorAtom) !void {
                if (self.tensor_count >= self.tensors.len) return error.ContextTooSmall;
                self.tensors[self.tensor_count] = tensor;
                self.tensor_count += 1;
            }

            fn addAction(self: *Scratch, action: ActionAtom) !void {
                if (self.action_count >= self.actions.len) return error.ContextTooSmall;
                self.actions[self.action_count] = action;
                self.action_count += 1;
            }
        };

        fn walk(left: Monomial, right: Monomial, projection: Projection, force_all_contracted: bool, left_index: usize, state: *Scratch, sink: anytype) !void {
            if (left_index == left.factors.len) {
                try emitSurvivors(left, right, projection, state, sink);
                return;
            }

            const left_factor = left.factors[left_index];
            if (!force_all_contracted and !hasCompleteResidualRuleForAvailableRight(left_factor.field, right, state)) {
                try walk(left, right, projection, force_all_contracted, left_index + 1, state, sink);
            }

            for (right.factors, 0..) |right_factor, right_index| {
                if (state.contracted_right[right_index]) continue;
                const rule = findRule(left_factor.field, right_factor.field) orelse continue;
                for (rule.terms) |term| {
                    const saved = state.*;
                    state.contracted_left[left_index] = true;
                    state.contracted_right[right_index] = true;
                    if (contractionIsOdd(left, right, left_index, right_index, &saved)) try state.scalar.mulRational(-1, 1);
                    try applyWickTerm(term, left_factor, right_factor, state);
                    try walk(left, right, projection, force_all_contracted, left_index + 1, state, sink);
                    state.* = saved;
                }
            }
        }

        fn emitSurvivors(left: Monomial, right: Monomial, projection: Projection, state: *Scratch, sink: anytype) !void {
            const saved_output = state.output_count;
            try appendRightSurvivors(right, state);
            try appendLeftTaylor(left, projection, 0, 0, state, sink);
            state.output_count = saved_output;
        }

        fn appendRightSurvivors(right: Monomial, state: *Scratch) !void {
            for (right.factors, 0..) |factor, index| {
                if (!state.contracted_right[index]) try state.addOutput(factor);
            }
        }

        fn appendLeftTaylor(left: Monomial, projection: Projection, index: usize, used_level: u8, state: *Scratch, sink: anytype) !void {
            if (index == left.factors.len) {
                try emitNormalOrdered(projection, used_level, state, sink);
                return;
            }
            if (state.contracted_left[index]) {
                try appendLeftTaylor(left, projection, index + 1, used_level, state, sink);
                return;
            }
            var extra: u8 = 0;
            while (used_level + extra <= projection.max_taylor_level) : (extra += 1) {
                const saved_output = state.output_count;
                const saved_coord = state.coordinate_count;
                const saved_scalar = state.scalar;
                var shifted = left.factors[index];
                shifted.derivative += extra;
                try state.addOutput(shifted);
                if (extra != 0) {
                    try state.scalar.mulRational(1, factorial(extra));
                    try state.addCoordinate(.{ .local_power = .{ .source_index = @intCast(index), .power = extra } });
                }
                try appendLeftTaylor(left, projection, index + 1, used_level + extra, state, sink);
                state.output_count = saved_output;
                state.coordinate_count = saved_coord;
                state.scalar = saved_scalar;
            }
        }

        fn emitNormalOrdered(projection: Projection, taylor_level: u8, state: *Scratch, sink: anytype) !void {
            var ordered: [limits.max_output_factors]OutputFactor = undefined;
            @memcpy(ordered[0..state.output_count], state.output[0..state.output_count]);
            var sign: i64 = 1;
            if (!canonicalizeOutput(ordered[0..state.output_count], &sign)) return;
            if (outputWeightTicks(ordered[0..state.output_count]) != projection.target_holomorphic_ticks) return;
            var scalar = state.scalar;
            if (sign < 0) try scalar.mulRational(-1, 1);
            const term = TermView{
                .scalar = scalar,
                .coordinates = state.coordinates[0..state.coordinate_count],
                .tensors = state.tensors[0..state.tensor_count],
                .actions = state.actions[0..state.action_count],
                .output = ordered[0..state.output_count],
                .branch_level = state.branch_level + taylor_level,
            };
            try sink.emitOpeTerm(term);
        }

        fn applyWickTerm(term: descriptor.WickTerm, left: PrimitiveFactor, right: PrimitiveFactor, state: *Scratch) !void {
            for (term.scalars) |factor| try state.scalar.mulFactor(d, limits, factor);
            for (term.coordinates) |coordinate| try applyCoordinate(coordinate, left, right, state);
            for (term.tensors) |tensor| try state.addTensor(try resolveTensor(tensor, left, right));
            for (term.actions) |action| try state.addAction(try resolveAction(action, left, right));
            for (term.residuals) |side| switch (side) {
                .left => try state.addOutput(left),
                .right => try state.addOutput(right),
            };
        }

        fn resolveTensor(tensor: descriptor.TensorFactor, left: PrimitiveFactor, right: PrimitiveFactor) !TensorAtom {
            return switch (tensor) {
                .none => .none,
                .metric => |item| .{ .metric = .{
                    .left = try labelValue(item.left, left, right),
                    .right = try labelValue(item.right, left, right),
                } },
                .momentum_index => |item| .{ .momentum_index = .{
                    .momentum = try labelValue(item.momentum, left, right),
                    .index = try labelValue(item.index, left, right),
                } },
                .momentum_pair => |item| .{ .momentum_pair = .{
                    .left = try labelValue(item.left, left, right),
                    .right = try labelValue(item.right, left, right),
                } },
            };
        }

        fn resolveAction(action: descriptor.ActionFactor, left: PrimitiveFactor, right: PrimitiveFactor) !ActionAtom {
            return switch (action) {
                .profile_derivative => |item| .{ .profile_derivative = .{
                    .profile = try labelValue(item.profile, left, right),
                    .index = try labelValue(item.index, left, right),
                } },
            };
        }

        fn labelValue(ref: descriptor.LabelRef, left: PrimitiveFactor, right: PrimitiveFactor) !u32 {
            const source = if (ref.side == .left) left.labels else right.labels;
            if (ref.slot >= source.len) return error.InvalidLabel;
            return source[ref.slot];
        }

        fn applyCoordinate(coordinate: descriptor.CoordinateFactor, left: PrimitiveFactor, right: PrimitiveFactor, state: *Scratch) !void {
            switch (coordinate) {
                .difference_power => |item| {
                    const left_derivatives = if (item.derive_left) left.derivative else 0;
                    const right_derivatives = if (item.derive_right) right.derivative else 0;
                    const total_derivatives: u8 = left_derivatives + right_derivatives;
                    try state.scalar.mulRational(derivativeCoefficient(item.exponent, total_derivatives), 1);
                    if ((right_derivatives & 1) != 0) try state.scalar.mulRational(-1, 1);
                    try state.addCoordinate(.{ .difference_power = .{
                        .left_slot = item.left.slot,
                        .right_slot = item.right.slot,
                        .exponent = item.exponent - @as(i16, total_derivatives),
                        .left_derivatives = left_derivatives,
                        .right_derivatives = right_derivatives,
                    } });
                },
                .logarithm => |item| try state.addCoordinate(.{ .logarithm = .{
                    .left_slot = item.left.slot,
                    .right_slot = item.right.slot,
                    .left_derivatives = if (item.derive_left) left.derivative else 0,
                    .right_derivatives = if (item.derive_right) right.derivative else 0,
                } }),
                .named_kernel => |item| try state.addCoordinate(.{ .named_kernel = .{
                    .symbol = item.symbol,
                    .left_slot = item.left.slot,
                    .right_slot = item.right.slot,
                    .left_derivatives = if (item.derive_left) left.derivative else 0,
                    .right_derivatives = if (item.derive_right) right.derivative else 0,
                } }),
                .green_exponential => |item| try state.addCoordinate(.{ .green_exponential = .{
                    .left_slot = item.left.slot,
                    .right_slot = item.right.slot,
                } }),
            }
        }

        fn findRule(left: descriptor.Id, right: descriptor.Id) ?descriptor.WickRule {
            inline for (d.wick_rules) |rule| {
                if (rule.left == left and rule.right == right) return rule;
            }
            return null;
        }

        fn hasCompleteResidualRuleForAvailableRight(left: descriptor.Id, right: Monomial, state: *const Scratch) bool {
            for (right.factors, 0..) |factor, index| {
                if (state.contracted_right[index]) continue;
                const rule = findRule(left, factor.field) orelse continue;
                if (isCompleteResidualRule(rule)) return true;
            }
            return false;
        }

        fn isCompleteResidualRule(rule: descriptor.WickRule) bool {
            if (rule.terms.len == 0) return false;
            for (rule.terms) |term| {
                if (term.residuals.len == 0) return false;
                var has_green_exponential = false;
                for (term.coordinates) |coordinate| {
                    if (std.meta.activeTag(coordinate) == .green_exponential) has_green_exponential = true;
                }
                if (!has_green_exponential) return false;
            }
            return true;
        }

        fn fieldIsFermionic(field: descriptor.Id) bool {
            return d.fields[field].statistics == .fermionic;
        }

        fn contractionIsOdd(left: Monomial, right: Monomial, left_index: usize, right_index: usize, state: *const Scratch) bool {
            if (!fieldIsFermionic(left.factors[left_index].field) or !fieldIsFermionic(right.factors[right_index].field)) return false;
            var count: usize = 0;
            for (left.factors[left_index + 1 ..], left_index + 1..) |factor, index| {
                if (!state.contracted_left[index] and fieldIsFermionic(factor.field)) count += 1;
            }
            for (right.factors[0..right_index], 0..) |factor, index| {
                if (!state.contracted_right[index] and fieldIsFermionic(factor.field)) count += 1;
            }
            return (count & 1) != 0;
        }

        fn canonicalizeOutput(output: []OutputFactor, sign: *i64) bool {
            var index: usize = 1;
            while (index < output.len) : (index += 1) {
                var cursor = index;
                while (cursor > 0 and outputLessThan(output[cursor], output[cursor - 1])) : (cursor -= 1) {
                    if (fieldIsFermionic(output[cursor].field) and fieldIsFermionic(output[cursor - 1].field)) sign.* = -sign.*;
                    std.mem.swap(OutputFactor, &output[cursor], &output[cursor - 1]);
                }
            }
            for (output[0..output.len -| 1], 0..) |factor, i| {
                if (factorEqual(factor, output[i + 1]) and fieldIsFermionic(factor.field)) return false;
            }
            return true;
        }

        fn outputLessThan(left: OutputFactor, right: OutputFactor) bool {
            if (left.field != right.field) return left.field < right.field;
            if (left.derivative != right.derivative) return left.derivative < right.derivative;
            return labelsLessThan(left.labels, right.labels);
        }

        fn labelsLessThan(left: []const u32, right: []const u32) bool {
            const n = @min(left.len, right.len);
            for (left[0..n], right[0..n]) |a, b| {
                if (a != b) return a < b;
            }
            return left.len < right.len;
        }

        fn factorEqual(left: OutputFactor, right: OutputFactor) bool {
            return left.field == right.field and left.derivative == right.derivative and std.mem.eql(u32, left.labels, right.labels);
        }

        fn survivorProjectionPossible(left: Monomial, right: Monomial, projection: Projection) bool {
            const total = left.factors.len + right.factors.len;
            if (total == 0 or total > @bitSizeOf(u32)) return true;
            const masks = (@as(u32, 1) << @intCast(total)) - 1;
            var mask: u32 = 1;
            while (mask <= masks) : (mask += 1) {
                var weight: i32 = 0;
                var left_survivors: usize = 0;
                var right_survivors: usize = 0;
                var index: usize = 0;
                while (index < total) : (index += 1) {
                    if (((mask >> @intCast(index)) & 1) == 0) continue;
                    const is_left = index < left.factors.len;
                    const factor = if (is_left) left.factors[index] else right.factors[index - left.factors.len];
                    if (is_left) {
                        left_survivors += 1;
                    } else {
                        right_survivors += 1;
                    }
                    weight += factorWeightTicks(factor);
                }
                if (weight != projection.target_holomorphic_ticks) continue;
                if (left.factors.len - left_survivors != right.factors.len - right_survivors) continue;
                return true;
            }
            return false;
        }

        fn outputWeightTicks(output: []const OutputFactor) i32 {
            var total: i32 = 0;
            for (output) |factor| total += factorWeightTicks(factor);
            return total;
        }

        fn factorWeightTicks(factor: OutputFactor) i32 {
            return fieldWeightTicks(factor.field) + @as(i32, factor.derivative) * tickDenominator();
        }

        fn tickDenominator() i32 {
            return if (d.basis) |basis| @intCast(basis.tick_denominator) else 1;
        }

        fn fieldWeightTicks(field: descriptor.Id) i32 {
            const metadata_id = d.fields[field].weight orelse return 0;
            return switch (d.metadata[metadata_id]) {
                .rational => |value| rationalTicks(value),
                .scalar_monomial => |value| rationalTicks(value.rational),
                else => 0,
            };
        }

        fn rationalTicks(value: descriptor.Rational) i32 {
            const den = value.denominator;
            if (den == 0) return 0;
            const numerator = value.numerator * tickDenominator();
            if (@rem(numerator, den) != 0) return 0;
            return @intCast(@divExact(numerator, den));
        }

    };
}

fn derivativeCoefficient(exponent: i16, derivative_count: u8) i64 {
    var result: i64 = 1;
    var step: u8 = 0;
    while (step < derivative_count) : (step += 1) {
        result *= @as(i64, exponent) - step;
    }
    return result;
}

fn factorial(value: u8) i64 {
    var result: i64 = 1;
    var n: u8 = 2;
    while (n <= value) : (n += 1) result *= n;
    return result;
}

test "generic OPE streams bc derivative matchings from descriptor rules" {
    const Kernel = GenericKernel(BenchmarkDescriptors.bc, .{ .max_factors = 4, .max_output_factors = 4 });
    const b: descriptor.Id = 0;
    const c: descriptor.Id = 1;
    const left_factors = [_]PrimitiveFactor{ .{ .field = b }, .{ .field = b, .derivative = 1 } };
    const right_factors = [_]PrimitiveFactor{ .{ .field = c }, .{ .field = c, .derivative = 1 } };
    const left_terms = [_]Monomial{.{ .factors = &left_factors }};
    const right_terms = [_]Monomial{.{ .factors = &right_factors }};
    var sink = CountHashSink{};

    try Kernel.opeProjected(.{ .terms = &left_terms }, .{ .terms = &right_terms }, .{}, &sink);

    try std.testing.expectEqual(@as(usize, 2), sink.term_count);
    try std.testing.expect(sink.hash != 0);
}

test "generic OPE differentiates descriptor pole kernels" {
    const Kernel = GenericKernel(BenchmarkDescriptors.bc, .{ .max_factors = 1, .max_output_factors = 1 });
    const left_factors = [_]PrimitiveFactor{.{ .field = 0, .derivative = 1 }};
    const right_factors = [_]PrimitiveFactor{.{ .field = 1, .derivative = 2 }};
    const left_terms = [_]Monomial{.{ .factors = &left_factors }};
    const right_terms = [_]Monomial{.{ .factors = &right_factors }};
    var sink = CountHashSink{};

    try Kernel.opeProjected(.{ .terms = &left_terms }, .{ .terms = &right_terms }, .{}, &sink);

    try std.testing.expectEqual(@as(usize, 1), sink.term_count);
}
