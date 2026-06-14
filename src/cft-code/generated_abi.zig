const std = @import("std");
const descriptor = @import("correlators/descriptor.zig");
const dispatch = @import("correlators/generated_dispatch.zig");
const kernel = @import("kernel.zig");
const presets = @import("presets.zig");
const basis_generation = @import("basis-generation/basis-generation.zig");
const cft_ope = @import("ope/ope.zig");

const allocator = std.heap.c_allocator;
const TheoryId = dispatch.TheoryId;
const ContextTag = dispatch.ContextTag;

/// Context is an opaque generated-theory runtime handle for the C ABI.
const Context = struct {
    inner: ContextTag,
    frozen: ?kernel.Call.MultiOp = null,
};

/// Event is one stable C ABI result event.
pub const Event = extern struct {
    kind: u8,
    a: u32,
    b: u32,
    c: u32,
    d: i32,
    name_ptr: ?[*]const u8,
    name_len: usize,
};

/// ExpressionTerm is one product in the expanded symbolic sum.
pub const ExpressionTerm = extern struct {
    first_factor: usize,
    factor_count: usize,
};

/// ExpressionFactor is one nontrivial symbolic product factor.
pub const ExpressionFactor = extern struct {
    kind: u8,
    a: u32,
    b: u32,
    c: u32,
    d: i32,
    name_id: u32,
};

/// ExpressionName is one borrowed symbolic name used by expression factors.
pub const ExpressionName = extern struct {
    ptr: ?[*]const u8,
    len: usize,
};

/// OpeTerm is one reusable OPE expression product.
pub const OpeTerm = extern struct {
    first_factor: usize,
    factor_count: usize,
    branch_level: u8,
};

/// OpeFactor is one compact coefficient or output-operator OPE factor.
pub const OpeFactor = extern struct {
    kind: u8,
    a: u32,
    b: u32,
    c: u32,
    d: i64,
    e: i64,
    name_id: u32,
};

/// OpeEvent is one stable compact streamed OPE record.
pub const OpeEvent = extern struct {
    kind: u8,
    a: u32,
    b: u32,
    c: u32,
    d: i64,
    e: i64,
    name_ptr: ?[*]const u8,
    name_len: usize,
};

/// EventCallback receives one streamed result event.
pub const EventCallback = *const fn (?*anyopaque, *const Event) callconv(.c) c_int;

/// EventChunkCallback receives a bounded chunk of streamed result events.
pub const EventChunkCallback = *const fn (?*anyopaque, [*]const Event, usize) callconv(.c) c_int;

/// OpeEventChunkCallback receives a bounded chunk of compact OPE records.
pub const OpeEventChunkCallback = *const fn (?*anyopaque, [*]const OpeEvent, usize) callconv(.c) c_int;

/// BasisQuantumFilter is one dense slot/value query constraint.
pub const BasisQuantumFilter = extern struct {
    slot: u8,
    value: i32,
};

/// BasisMode is one borrowed compact mode in a streamed basis candidate.
pub const BasisMode = extern struct {
    mode_index: u32,
    id: u32,
    component: u16,
    label: u16,
    weight_ticks: u32,
    body: u32,
    name_ptr: ?[*]const u8,
    name_len: usize,
};

/// BasisRecord is valid only for the duration of the compact callback.
pub const BasisRecord = extern struct {
    presentation: u16,
    seed: u16,
    seed_body: u32,
    base_weight_ticks: i32,
    weight_ticks: i32,
    level_ticks: u32,
    base_quantum_ptr: ?[*]const i32,
    base_quantum_len: usize,
    quantum_ptr: ?[*]const i32,
    quantum_len: usize,
    mode_ptr: ?[*]const BasisMode,
    mode_len: usize,
};

/// BasisCallback receives one compact streamed basis candidate.
pub const BasisCallback = *const fn (?*anyopaque, *const BasisRecord) callconv(.c) c_int;

const StreamState = struct {
    payload: ?*anyopaque,
    callback: EventCallback,
};

const event_chunk_capacity = 256;

const BufferedStreamState = struct {
    payload: ?*anyopaque,
    callback: EventChunkCallback,
    events: [event_chunk_capacity]Event = undefined,
    len: usize = 0,

    fn flush(self: *@This()) !void {
        if (self.len == 0) return;
        if (self.callback(self.payload, &self.events, self.len) != 0) return error.CallbackFailed;
        self.len = 0;
    }

    fn push(self: *@This(), event: Event) !void {
        self.events[self.len] = event;
        self.len += 1;
        if (self.len == self.events.len) try self.flush();
    }
};

fn abiEvent(event: descriptor.ResultEvent) Event {
    const name_ptr: ?[*]const u8 = if (event.name) |name| name.ptr else null;
    const name_len: usize = if (event.name) |name| name.len else 0;
    return .{
        .kind = @intFromEnum(event.kind),
        .a = event.a,
        .b = event.b,
        .c = event.c,
        .d = event.d,
        .name_ptr = name_ptr,
        .name_len = name_len,
    };
}

fn streamThunk(payload: *anyopaque, event: descriptor.ResultEvent) !void {
    const state: *StreamState = @ptrCast(@alignCast(payload));
    const stable_event = abiEvent(event);
    if (state.callback(state.payload, &stable_event) != 0) return error.CallbackFailed;
}

fn bufferedStreamThunk(payload: *anyopaque, event: descriptor.ResultEvent) !void {
    const state: *BufferedStreamState = @ptrCast(@alignCast(payload));
    try state.push(abiEvent(event));
}

const NameKey = struct {
    ptr: usize,
    len: usize,
};

const ExpressionRecordState = struct {
    terms: std.ArrayList(ExpressionTerm) = .empty,
    factors: std.ArrayList(ExpressionFactor) = .empty,
    names: std.ArrayList(ExpressionName) = .empty,
    name_ids: std.AutoHashMap(NameKey, u32) = std.AutoHashMap(NameKey, u32).init(allocator),
    term_start: usize = 0,

    fn deinit(self: *@This()) void {
        self.terms.deinit(allocator);
        self.factors.deinit(allocator);
        self.names.deinit(allocator);
        self.name_ids.deinit();
    }

    fn nameId(self: *@This(), maybe_name: ?[]const u8) !u32 {
        const name = maybe_name orelse return 0;
        const key = NameKey{ .ptr = @intFromPtr(name.ptr), .len = name.len };
        if (self.name_ids.get(key)) |id| return id;
        const id: u32 = @intCast(self.names.items.len + 1);
        try self.names.append(allocator, .{ .ptr = name.ptr, .len = name.len });
        try self.name_ids.put(key, id);
        return id;
    }

    fn finishTerm(self: *@This()) !void {
        try self.terms.append(allocator, .{
            .first_factor = self.term_start,
            .factor_count = self.factors.items.len - self.term_start,
        });
        self.term_start = self.factors.items.len;
    }

    fn pushFactor(self: *@This(), event: descriptor.ResultEvent) !void {
        if (event.kind == .scalar and event.d == 0 and event.name == null) return;
        try self.factors.append(allocator, .{
            .kind = @intFromEnum(event.kind),
            .a = event.a,
            .b = event.b,
            .c = event.c,
            .d = event.d,
            .name_id = try self.nameId(event.name),
        });
    }
};

fn expressionRecordThunk(payload: *anyopaque, event: descriptor.ResultEvent) !void {
    const state: *ExpressionRecordState = @ptrCast(@alignCast(payload));
    switch (event.kind) {
        .sum_term_begin => state.term_start = state.factors.items.len,
        .sum_term_end => try state.finishTerm(),
        .wick_term_begin, .wick_term_end => {},
        .scalar, .coordinate, .tensor, .zero_mode, .residual_operator => try state.pushFactor(event),
    }
}

const OpeFactorKind = struct {
    const term_begin: u8 = 250;
    const term_end: u8 = 251;
    const scalar_rational: u8 = 0;
    const scalar_i: u8 = 1;
    const scalar_atom: u8 = 2;
    const coordinate_difference: u8 = 3;
    const coordinate_named: u8 = 4;
    const coordinate_exp_green: u8 = 5;
    const coordinate_local_power: u8 = 6;
    const tensor_metric: u8 = 10;
    const tensor_momentum_index: u8 = 11;
    const tensor_momentum_pair: u8 = 12;
    const action_profile_derivative: u8 = 13;
    const output_field: u8 = 20;
    const output_label: u8 = 21;
};

const ope_event_chunk_capacity = 2048;

const OpeBufferedStreamState = struct {
    theory: TheoryId,
    left_coords: []const u32,
    right_coord: u32,
    payload: ?*anyopaque,
    callback: OpeEventChunkCallback,
    events: [ope_event_chunk_capacity]OpeEvent = undefined,
    len: usize = 0,

    fn flush(self: *@This()) !void {
        if (self.len == 0) return;
        if (self.callback(self.payload, &self.events, self.len) != 0) return error.CallbackFailed;
        self.len = 0;
    }

    fn push(self: *@This(), event: OpeEvent) !void {
        self.events[self.len] = event;
        self.len += 1;
        if (self.len == self.events.len) try self.flush();
    }

    fn pushNamed(self: *@This(), kind: u8, a: u32, b: u32, c: u32, d: i64, e: i64, name: ?[]const u8) !void {
        _ = name;
        try self.push(.{
            .kind = kind,
            .a = a,
            .b = b,
            .c = c,
            .d = d,
            .e = e,
            .name_ptr = null,
            .name_len = 0,
        });
    }

    fn leftCoord(self: *@This(), index: usize) u32 {
        if (self.left_coords.len == 0) return self.right_coord;
        if (index < self.left_coords.len) return self.left_coords[index];
        return self.left_coords[0];
    }

    fn pushScalar(self: *@This(), scalar: cft_ope.Scalar) !void {
        if (scalar.numerator != 1 or scalar.denominator != 1) {
            try self.pushNamed(OpeFactorKind.scalar_rational, @intCast(scalar.denominator), 0, 0, @intCast(scalar.numerator), 0, null);
        }
        if (scalar.imaginary_power != 0) {
            try self.pushNamed(OpeFactorKind.scalar_i, scalar.imaginary_power, 0, 0, 0, 0, null);
        }
        for (scalar.atoms[0..scalar.atom_count]) |atom| {
            try self.pushNamed(OpeFactorKind.scalar_atom, atom.symbol, 0, 0, atom.power, 0, dispatch.descriptorSymbolName(self.theory, atom.symbol));
        }
    }

    fn pushCoordinate(self: *@This(), coordinate: cft_ope.CoordinateAtom) !void {
        switch (coordinate) {
            .difference_power => |item| try self.pushNamed(
                OpeFactorKind.coordinate_difference,
                self.leftCoord(0),
                self.right_coord,
                (@as(u32, item.left_derivatives) << 16) | item.right_derivatives,
                item.exponent,
                0,
                null,
            ),
            .logarithm => |item| try self.pushNamed(
                OpeFactorKind.coordinate_named,
                self.leftCoord(0),
                self.right_coord,
                (@as(u32, item.left_derivatives) << 16) | item.right_derivatives,
                0,
                0,
                "log",
            ),
            .named_kernel => |item| try self.pushNamed(
                OpeFactorKind.coordinate_named,
                self.leftCoord(0),
                self.right_coord,
                (@as(u32, item.left_derivatives) << 16) | item.right_derivatives,
                0,
                0,
                dispatch.descriptorSymbolName(self.theory, item.symbol),
            ),
            .green_exponential => try self.pushNamed(OpeFactorKind.coordinate_exp_green, self.leftCoord(0), self.right_coord, 0, 0, 0, "exp-green"),
            .local_power => |item| try self.pushNamed(OpeFactorKind.coordinate_local_power, self.leftCoord(item.source_index), self.right_coord, 0, item.power, 0, null),
        }
    }

    fn pushTensor(self: *@This(), tensor: cft_ope.TensorAtom) !void {
        switch (tensor) {
            .none => {},
            .metric => |item| try self.pushNamed(OpeFactorKind.tensor_metric, item.left, item.right, 0, 0, 0, "metric"),
            .momentum_index => |item| try self.pushNamed(OpeFactorKind.tensor_momentum_index, item.momentum, item.index, 0, 0, 0, "momentum-index"),
            .momentum_pair => |item| try self.pushNamed(OpeFactorKind.tensor_momentum_pair, item.left, item.right, 0, 0, 0, "momentum-pair"),
        }
    }

    fn pushAction(self: *@This(), action: cft_ope.ActionAtom) !void {
        switch (action) {
            .profile_derivative => |item| try self.pushNamed(OpeFactorKind.action_profile_derivative, item.profile, item.index, 0, 0, 0, "profile-derivative"),
        }
    }

    fn pushOutput(self: *@This(), output: []const cft_ope.OutputFactor) !void {
        for (output) |factor| {
            try self.pushNamed(
                OpeFactorKind.output_field,
                factor.field,
                self.right_coord,
                factor.derivative,
                @intCast(factor.labels.len),
                0,
                dispatch.fieldName(self.theory, factor.field),
            );
            for (factor.labels) |label| {
                try self.pushNamed(OpeFactorKind.output_label, label, 0, 0, 0, 0, null);
            }
        }
    }

    pub fn emitOpeTerm(self: *@This(), term: cft_ope.TermView) !void {
        try self.pushNamed(OpeFactorKind.term_begin, term.branch_level, 0, 0, 0, 0, null);
        try self.pushScalar(term.scalar);
        for (term.coordinates) |coordinate| try self.pushCoordinate(coordinate);
        for (term.tensors) |tensor| try self.pushTensor(tensor);
        for (term.actions) |action| try self.pushAction(action);
        try self.pushOutput(term.output);
        try self.pushNamed(OpeFactorKind.term_end, term.branch_level, 0, 0, 0, 0, null);
    }
};

const OpeRecordState = struct {
    theory: TheoryId,
    left_coords: []const u32,
    right_coord: u32,
    terms: std.ArrayList(OpeTerm) = .empty,
    factors: std.ArrayList(OpeFactor) = .empty,
    names: std.ArrayList(ExpressionName) = .empty,
    name_ids: std.AutoHashMap(NameKey, u32) = std.AutoHashMap(NameKey, u32).init(allocator),

    fn deinit(self: *@This()) void {
        self.terms.deinit(allocator);
        self.factors.deinit(allocator);
        self.names.deinit(allocator);
        self.name_ids.deinit();
    }

    fn nameId(self: *@This(), maybe_name: ?[]const u8) !u32 {
        const name = maybe_name orelse return 0;
        const key = NameKey{ .ptr = @intFromPtr(name.ptr), .len = name.len };
        if (self.name_ids.get(key)) |id| return id;
        const id: u32 = @intCast(self.names.items.len + 1);
        try self.names.append(allocator, .{ .ptr = name.ptr, .len = name.len });
        try self.name_ids.put(key, id);
        return id;
    }

    fn push(self: *@This(), factor: OpeFactor) !void {
        try self.factors.append(allocator, factor);
    }

    fn pushScalar(self: *@This(), scalar: cft_ope.Scalar) !void {
        if (scalar.numerator != 1 or scalar.denominator != 1) {
            try self.push(.{
                .kind = OpeFactorKind.scalar_rational,
                .a = @intCast(scalar.denominator),
                .b = 0,
                .c = 0,
                .d = @intCast(scalar.numerator),
                .e = 0,
                .name_id = 0,
            });
        }
        if (scalar.imaginary_power != 0) {
            try self.push(.{
                .kind = OpeFactorKind.scalar_i,
                .a = scalar.imaginary_power,
                .b = 0,
                .c = 0,
                .d = 0,
                .e = 0,
                .name_id = 0,
            });
        }
        for (scalar.atoms[0..scalar.atom_count]) |atom| {
            try self.push(.{
                .kind = OpeFactorKind.scalar_atom,
                .a = atom.symbol,
                .b = 0,
                .c = 0,
                .d = atom.power,
                .e = 0,
                .name_id = 0,
            });
        }
    }

    fn pushCoordinate(self: *@This(), coordinate: cft_ope.CoordinateAtom) !void {
        switch (coordinate) {
            .difference_power => |item| try self.push(.{
                .kind = OpeFactorKind.coordinate_difference,
                .a = self.leftCoord(0),
                .b = self.right_coord,
                .c = (@as(u32, item.left_derivatives) << 16) | item.right_derivatives,
                .d = item.exponent,
                .e = 0,
                .name_id = 0,
            }),
            .logarithm => |item| try self.push(.{
                .kind = OpeFactorKind.coordinate_named,
                .a = self.leftCoord(0),
                .b = self.right_coord,
                .c = (@as(u32, item.left_derivatives) << 16) | item.right_derivatives,
                .d = 0,
                .e = 0,
                .name_id = try self.nameId("log"),
            }),
            .named_kernel => |item| try self.push(.{
                .kind = OpeFactorKind.coordinate_named,
                .a = self.leftCoord(0),
                .b = self.right_coord,
                .c = (@as(u32, item.left_derivatives) << 16) | item.right_derivatives,
                .d = 0,
                .e = 0,
                .name_id = try self.nameId(dispatch.descriptorSymbolName(self.theory, item.symbol)),
            }),
            .green_exponential => try self.push(.{
                .kind = OpeFactorKind.coordinate_exp_green,
                .a = self.leftCoord(0),
                .b = self.right_coord,
                .c = 0,
                .d = 0,
                .e = 0,
                .name_id = try self.nameId("exp-green"),
            }),
            .local_power => |item| try self.push(.{
                .kind = OpeFactorKind.coordinate_local_power,
                .a = self.leftCoord(item.source_index),
                .b = self.right_coord,
                .c = 0,
                .d = item.power,
                .e = 0,
                .name_id = 0,
            }),
        }
    }

    fn pushTensor(self: *@This(), tensor: cft_ope.TensorAtom) !void {
        switch (tensor) {
            .none => {},
            .metric => |item| try self.push(.{
                .kind = OpeFactorKind.tensor_metric,
                .a = item.left,
                .b = item.right,
                .c = 0,
                .d = 0,
                .e = 0,
                .name_id = try self.nameId("metric"),
            }),
            .momentum_index => |item| try self.push(.{
                .kind = OpeFactorKind.tensor_momentum_index,
                .a = item.momentum,
                .b = item.index,
                .c = 0,
                .d = 0,
                .e = 0,
                .name_id = try self.nameId("momentum-index"),
            }),
            .momentum_pair => |item| try self.push(.{
                .kind = OpeFactorKind.tensor_momentum_pair,
                .a = item.left,
                .b = item.right,
                .c = 0,
                .d = 0,
                .e = 0,
                .name_id = try self.nameId("momentum-pair"),
            }),
        }
    }

    fn pushAction(self: *@This(), action: cft_ope.ActionAtom) !void {
        switch (action) {
            .profile_derivative => |item| try self.push(.{
                .kind = OpeFactorKind.action_profile_derivative,
                .a = item.profile,
                .b = item.index,
                .c = 0,
                .d = 0,
                .e = 0,
                .name_id = try self.nameId("profile-derivative"),
            }),
        }
    }

    fn pushOutput(self: *@This(), output: []const cft_ope.OutputFactor) !void {
        for (output) |factor| {
            try self.push(.{
                .kind = OpeFactorKind.output_field,
                .a = factor.field,
                .b = self.right_coord,
                .c = factor.derivative,
                .d = @intCast(factor.labels.len),
                .e = 0,
                .name_id = 0,
            });
            for (factor.labels) |label| {
                try self.push(.{
                    .kind = OpeFactorKind.output_label,
                    .a = label,
                    .b = 0,
                    .c = 0,
                    .d = 0,
                    .e = 0,
                    .name_id = 0,
                });
            }
        }
    }

    fn leftCoord(self: *@This(), index: usize) u32 {
        if (self.left_coords.len == 0) return self.right_coord;
        if (index < self.left_coords.len) return self.left_coords[index];
        return self.left_coords[0];
    }

    pub fn emitOpeTerm(self: *@This(), term: cft_ope.TermView) !void {
        const start = self.factors.items.len;
        try self.pushScalar(term.scalar);
        for (term.coordinates) |coordinate| try self.pushCoordinate(coordinate);
        for (term.tensors) |tensor| try self.pushTensor(tensor);
        for (term.actions) |action| try self.pushAction(action);
        try self.pushOutput(term.output);
        try self.terms.append(allocator, .{
            .first_factor = start,
            .factor_count = self.factors.items.len - start,
            .branch_level = term.branch_level,
        });
    }
};

var last_error_storage: [256]u8 = [_]u8{0} ** 256;

fn clearError() void {
    last_error_storage[0] = 0;
}

fn setErrorName(name: []const u8) c_int {
    const len = @min(name.len, last_error_storage.len - 1);
    @memcpy(last_error_storage[0..len], name[0..len]);
    last_error_storage[len] = 0;
    return -1;
}

fn setError(err: anyerror) c_int {
    return setErrorName(@errorName(err));
}

fn setErrorFmt(comptime format: []const u8, args: anytype) c_int {
    const text = std.fmt.bufPrint(last_error_storage[0 .. last_error_storage.len - 1], format, args) catch {
        return setErrorName("ErrorMessageTooLong");
    };
    last_error_storage[text.len] = 0;
    return -1;
}

fn validateFieldInsert(id: TheoryId, field_id: u16, coord_len: usize, label_len: usize) c_int {
    const name = dispatch.fieldName(id, field_id) orelse {
        return setErrorFmt("UnknownField id={d}", .{field_id});
    };
    const expected_coords = dispatch.fieldCoordinateArity(id, field_id).?;
    if (coord_len != expected_coords) {
        return setErrorFmt(
            "Field {s} expects {d} coordinates, got {d}",
            .{ name, expected_coords, coord_len },
        );
    }
    const expected_labels = dispatch.fieldLabelArity(id, field_id).?;
    if (label_len != expected_labels) {
        return setErrorFmt(
            "Field {s} expects {d} labels, got {d}",
            .{ name, expected_labels, label_len },
        );
    }
    return 0;
}

fn basisFilterSlice(ptr: ?[*]const BasisQuantumFilter, len: usize) ![]const BasisQuantumFilter {
    if (len == 0) return &.{};
    const data = ptr orelse return error.NullPointer;
    return data[0..len];
}

fn basisQuery(
    weight_kind: u8,
    weight_ticks: i32,
    max_word_length: u16,
    level_match: u8,
    filters_ptr: ?[*]const BasisQuantumFilter,
    filter_count: usize,
    filters_out: []basis_generation.QuantumFilter,
) !basis_generation.Query {
    const raw_filters = try basisFilterSlice(filters_ptr, filter_count);
    if (filters_out.len < raw_filters.len) return error.ContextTooSmall;
    for (raw_filters, 0..) |filter, index| {
        filters_out[index] = .{ .slot = filter.slot, .value = filter.value };
    }
    return .{
        .weight = switch (weight_kind) {
            0 => .{ .exact = weight_ticks },
            1 => .{ .max = weight_ticks },
            else => return error.InvalidQuery,
        },
        .quantum_filters = filters_out[0..raw_filters.len],
        .level_match = switch (level_match) {
            0 => null,
            1 => .{},
            else => return error.InvalidQuery,
        },
        .max_word_length = max_word_length,
    };
}

const abi_basis_max_level_ticks: u32 = 128;
const abi_basis_max_depth: usize = 64;
const abi_basis_max_filters: usize = 16;
const abi_basis_max_modes_per_candidate: usize = 64;
const abi_basis_product_pair_base: u32 = 1000;

fn basisProductPairId(left: u32, right: u32) u32 {
    return abi_basis_product_pair_base + left * 16 + right;
}

fn singleBasis(comptime raw_theory: u32) type {
    return dispatch.basis(@as(TheoryId, @enumFromInt(raw_theory)));
}

fn basisProductCompatible(comptime left: u32, comptime right: u32) bool {
    return dispatch.basisBackend(@as(TheoryId, @enumFromInt(left))).tick_denominator == dispatch.basisBackend(@as(TheoryId, @enumFromInt(right))).tick_denominator;
}

fn ProductPairBasis(comptime left: u32, comptime right: u32) type {
    return presets.product(.{ struct {
        pub const basis = singleBasis(left);
    }, struct {
        pub const basis = singleBasis(right);
    } }).basis;
}

fn productPairRun(comptime left: u32, comptime right: u32, query: basis_generation.Query, sink: anytype) !void {
    return basisRun(ProductPairBasis(left, right), query, sink);
}

fn productPairRenderTable(comptime left: u32, comptime right: u32) basis_generation.RenderTable {
    return ProductPairBasis(left, right).render_table;
}

fn basisWeightLimit(query: basis_generation.Query) i32 {
    return switch (query.weight) {
        .exact => |ticks| ticks,
        .max => |ticks| ticks,
    };
}

const BasisCountSink = struct {
    count: usize = 0,

    pub fn emitBasisState(self: *@This(), _: basis_generation.Candidate) !void {
        self.count += 1;
    }
};

const BasisCompactSink = struct {
    payload: ?*anyopaque,
    callback: BasisCallback,
    table: basis_generation.RenderTable,
    modes: [abi_basis_max_modes_per_candidate]BasisMode = undefined,

    fn modeName(self: *@This(), id: u32, component: u16) ?[]const u8 {
        if (self.table.modeAtom(id, component)) |atom| return atom.name;
        return null;
    }

    pub fn emitBasisState(self: *@This(), candidate: basis_generation.Candidate) !void {
        if (candidate.modes.len > self.modes.len) return error.ContextTooSmall;
        for (candidate.modes, 0..) |mode, index| {
            const name = self.modeName(mode.id, mode.component);
            self.modes[index] = .{
                .mode_index = mode.mode_index,
                .id = mode.id,
                .component = mode.component,
                .label = mode.label,
                .weight_ticks = mode.weight_ticks,
                .body = mode.body,
                .name_ptr = if (name) |value| value.ptr else null,
                .name_len = if (name) |value| value.len else 0,
            };
        }
        const record = BasisRecord{
            .presentation = candidate.presentation,
            .seed = candidate.seed,
            .seed_body = candidate.seed_body,
            .base_weight_ticks = candidate.base_weight_ticks,
            .weight_ticks = candidate.weight_ticks,
            .level_ticks = candidate.level_ticks,
            .base_quantum_ptr = if (candidate.base_quantum_values.len == 0) null else candidate.base_quantum_values.ptr,
            .base_quantum_len = candidate.base_quantum_values.len,
            .quantum_ptr = if (candidate.quantum_values.len == 0) null else candidate.quantum_values.ptr,
            .quantum_len = candidate.quantum_values.len,
            .mode_ptr = if (candidate.modes.len == 0) null else self.modes[0..candidate.modes.len].ptr,
            .mode_len = candidate.modes.len,
        };
        if (self.callback(self.payload, &record) != 0) return error.CallbackFailed;
    }
};

const AbiTextWriter = struct {
    bytes: *std.ArrayList(u8),

    pub fn writeAll(self: *@This(), data: []const u8) !void {
        try self.bytes.appendSlice(allocator, data);
    }
};

fn basisRunWithTicks(comptime Basis: type, comptime max_ticks: u32, query: basis_generation.Query, sink: anytype) !void {
    if (query.max_word_length > abi_basis_max_depth) return error.WordStackTooSmall;
    return Basis.stream(max_ticks, abi_basis_max_depth, query, sink);
}

fn basisRun(comptime Basis: type, query: basis_generation.Query, sink: anytype) !void {
    const limit = basisWeightLimit(query);
    if (limit > @as(i32, @intCast(abi_basis_max_level_ticks - 1))) return error.ContextTooSmall;
    if (limit <= 4) return basisRunWithTicks(Basis, 8, query, sink);
    if (limit <= 16) return basisRunWithTicks(Basis, 16, query, sink);
    if (limit <= 32) return basisRunWithTicks(Basis, 32, query, sink);
    if (limit <= 64) return basisRunWithTicks(Basis, 64, query, sink);
    return basisRunWithTicks(Basis, abi_basis_max_level_ticks, query, sink);
}

fn dispatchProductBasis(raw_theory: u32, query: basis_generation.Query, sink: anytype) !bool {
    inline for (std.meta.fields(TheoryId)) |left_field| {
        inline for (std.meta.fields(TheoryId)) |right_field| {
            const left: u32 = left_field.value;
            const right: u32 = right_field.value;
            if (basisProductCompatible(left, right) and raw_theory == basisProductPairId(left, right)) {
                try productPairRun(left, right, query, sink);
                return true;
            }
        }
    }
    return false;
}

fn dispatchBasis(raw_theory: u32, query: basis_generation.Query, sink: anytype) !void {
    if (try dispatchProductBasis(raw_theory, query, sink)) return;
    const id = try dispatch.theoryId(raw_theory);
    return switch (id) {
        inline else => |case| basisRun(singleBasis(@intFromEnum(case)), query, sink),
    };
}

fn productBasisRenderTable(raw_theory: u32) ?basis_generation.RenderTable {
    inline for (std.meta.fields(TheoryId)) |left_field| {
        inline for (std.meta.fields(TheoryId)) |right_field| {
            const left: u32 = left_field.value;
            const right: u32 = right_field.value;
            if (basisProductCompatible(left, right) and raw_theory == basisProductPairId(left, right)) {
                return productPairRenderTable(left, right);
            }
        }
    }
    return null;
}

fn basisRenderTable(raw_theory: u32) !basis_generation.RenderTable {
    if (productBasisRenderTable(raw_theory)) |table| return table;
    const id = try dispatch.theoryId(raw_theory);
    return switch (id) {
        inline else => |case| singleBasis(@intFromEnum(case)).render_table,
    };
}

/// sc_generated_basis_count returns the number of accepted compact basis states.
export fn sc_generated_basis_count(
    raw_theory: u32,
    weight_kind: u8,
    weight_ticks: i32,
    max_word_length: u16,
    level_match: u8,
    filters_ptr: ?[*]const BasisQuantumFilter,
    filter_count: usize,
    out_count: ?*usize,
) c_int {
    clearError();
    const out = out_count orelse return setErrorName("NullOutput");
    var filters: [abi_basis_max_filters]basis_generation.QuantumFilter = undefined;
    const query = basisQuery(weight_kind, weight_ticks, max_word_length, level_match, filters_ptr, filter_count, &filters) catch |err| return setError(err);
    var sink = BasisCountSink{};
    dispatchBasis(raw_theory, query, &sink) catch |err| return setError(err);
    out.* = sink.count;
    return 0;
}

/// sc_generated_basis_run_compact streams compact records without text rendering.
export fn sc_generated_basis_run_compact(
    raw_theory: u32,
    weight_kind: u8,
    weight_ticks: i32,
    max_word_length: u16,
    level_match: u8,
    filters_ptr: ?[*]const BasisQuantumFilter,
    filter_count: usize,
    payload: ?*anyopaque,
    callback: ?BasisCallback,
) c_int {
    clearError();
    const cb = callback orelse return setErrorName("NullCallback");
    var filters: [abi_basis_max_filters]basis_generation.QuantumFilter = undefined;
    const query = basisQuery(weight_kind, weight_ticks, max_word_length, level_match, filters_ptr, filter_count, &filters) catch |err| return setError(err);
    var sink = BasisCompactSink{
        .payload = payload,
        .callback = cb,
        .table = basisRenderTable(raw_theory) catch |err| return setError(err),
    };
    dispatchBasis(raw_theory, query, &sink) catch |err| return setError(err);
    return 0;
}

/// sc_generated_basis_text allocates bounded explicit REPL text output.
export fn sc_generated_basis_text(
    raw_theory: u32,
    weight_kind: u8,
    weight_ticks: i32,
    max_word_length: u16,
    level_match: u8,
    filters_ptr: ?[*]const BasisQuantumFilter,
    filter_count: usize,
    format: u8,
    max_states: usize,
    out_ptr: ?*?[*]u8,
    out_len: ?*usize,
) c_int {
    clearError();
    const ptr_out = out_ptr orelse return setErrorName("NullOutput");
    const len_out = out_len orelse return setErrorName("NullOutput");
    var filters: [abi_basis_max_filters]basis_generation.QuantumFilter = undefined;
    const query = basisQuery(weight_kind, weight_ticks, max_word_length, level_match, filters_ptr, filter_count, &filters) catch |err| return setError(err);
    var bytes: std.ArrayList(u8) = .empty;
    errdefer bytes.deinit(allocator);
    var writer = AbiTextWriter{ .bytes = &bytes };
    var sink = basis_generation.textSink(&writer, .{
        .format = switch (format) {
            0 => .compact,
            1 => .state,
            2 => .operator_at_zero,
            else => return setErrorName("InvalidQuery"),
        },
        .max_states = max_states,
    }, basisRenderTable(raw_theory) catch |err| return setError(err));
    dispatchBasis(raw_theory, query, &sink) catch |err| return setError(err);
    const owned = bytes.toOwnedSlice(allocator) catch |err| return setError(err);
    ptr_out.* = owned.ptr;
    len_out.* = owned.len;
    return 0;
}

/// sc_generated_basis_text_free releases text allocated by sc_generated_basis_text.
export fn sc_generated_basis_text_free(ptr: ?[*]u8, len: usize) void {
    if (ptr) |data| allocator.free(data[0..len]);
}

/// sc_generated_last_error returns the last ABI error string.
export fn sc_generated_last_error() [*:0]const u8 {
    return @ptrCast(&last_error_storage);
}

/// sc_generated_descriptor_abi_version returns the descriptor ABI version.
export fn sc_generated_descriptor_abi_version() u32 {
    return descriptor.descriptor_abi_version;
}

/// sc_generated_theory_hash returns the generated theory hash for a theory id.
export fn sc_generated_theory_hash(raw_theory: u32) u32 {
    clearError();
    const id = dispatch.theoryId(raw_theory) catch |err| {
        _ = setError(err);
        return 0;
    };
    return dispatch.theoryHash(id);
}

/// sc_generated_scalar_atom_name returns a descriptor parameter name for an atom id.
export fn sc_generated_scalar_atom_name(raw_theory: u32, atom: u32, out_ptr: ?*?[*]const u8, out_len: ?*usize) c_int {
    clearError();
    const id = dispatch.theoryId(raw_theory) catch |err| return setError(err);
    const ptr = out_ptr orelse return setErrorName("NullOutput");
    const len = out_len orelse return setErrorName("NullOutput");
    const name = dispatch.scalarAtomParameterName(id, atom) orelse return setErrorName("UnknownScalarAtom");
    ptr.* = name.ptr;
    len.* = name.len;
    return 0;
}

/// sc_generated_field_metadata returns descriptor field name and insertion arities.
export fn sc_generated_field_metadata(raw_theory: u32, field_id: u16, out_ptr: ?*?[*]const u8, out_len: ?*usize, out_coord_arity: ?*usize, out_label_arity: ?*usize) c_int {
    clearError();
    const id = dispatch.theoryId(raw_theory) catch |err| return setError(err);
    const ptr = out_ptr orelse return setErrorName("NullOutput");
    const len = out_len orelse return setErrorName("NullOutput");
    const coords = out_coord_arity orelse return setErrorName("NullOutput");
    const labels = out_label_arity orelse return setErrorName("NullOutput");
    const name = dispatch.fieldName(id, field_id) orelse {
        return setErrorFmt("UnknownField id={d}", .{field_id});
    };
    ptr.* = name.ptr;
    len.* = name.len;
    coords.* = dispatch.fieldCoordinateArity(id, field_id).?;
    labels.* = dispatch.fieldLabelArity(id, field_id).?;
    return 0;
}

/// sc_generated_context_create allocates a context for a generated theory id.
export fn sc_generated_context_create(raw_theory: u32) ?*Context {
    clearError();
    const id = dispatch.theoryId(raw_theory) catch |err| {
        _ = setError(err);
        return null;
    };
    const ctx = allocator.create(Context) catch |err| {
        _ = setError(err);
        return null;
    };
    ctx.* = .{ .inner = ContextTag.create(id) catch |err| {
        allocator.destroy(ctx);
        _ = setError(err);
        return null;
    } };
    return ctx;
}

/// sc_generated_context_destroy releases a generated context.
export fn sc_generated_context_destroy(ctx: ?*Context) void {
    const handle = ctx orelse return;
    handle.inner.destroy();
    allocator.destroy(handle);
}

fn byteSlice(ptr: ?[*]const u8, len: usize) ![]const u8 {
    const data = ptr orelse return error.NullPointer;
    return data[0..len];
}

fn u32Slice(ptr: ?[*]const u32, len: usize) ![]const u32 {
    if (len == 0) return &.{};
    const data = ptr orelse return error.NullPointer;
    return data[0..len];
}

/// sc_generated_symbol_intern interns a runtime symbol in one context.
export fn sc_generated_symbol_intern(ctx: ?*Context, name_ptr: ?[*]const u8, name_len: usize, out_symbol: ?*u32) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    const out = out_symbol orelse return setErrorName("NullOutput");
    const name = byteSlice(name_ptr, name_len) catch |err| return setError(err);
    out.* = handle.inner.symbolIntern(name) catch |err| return setError(err);
    return 0;
}

/// sc_generated_field_insert appends one generated field occurrence.
export fn sc_generated_field_insert(ctx: ?*Context, field_id: u16, coords_ptr: ?[*]const u32, coord_len: usize, labels_ptr: ?[*]const u32, label_len: usize) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    if (validateFieldInsert(std.meta.activeTag(handle.inner), field_id, coord_len, label_len) != 0) return -1;
    const coords = u32Slice(coords_ptr, coord_len) catch |err| return setError(err);
    const labels = u32Slice(labels_ptr, label_len) catch |err| return setError(err);
    handle.inner.fieldInsert(field_id, coords, labels) catch |err| return setError(err);
    handle.frozen = null;
    return 0;
}

/// sc_generated_field_insert_derivative appends one derivative field occurrence.
export fn sc_generated_field_insert_derivative(ctx: ?*Context, field_id: u16, coords_ptr: ?[*]const u32, coord_len: usize, labels_ptr: ?[*]const u32, label_len: usize, derivative: u8) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    if (validateFieldInsert(std.meta.activeTag(handle.inner), field_id, coord_len, label_len) != 0) return -1;
    const coords = u32Slice(coords_ptr, coord_len) catch |err| return setError(err);
    const labels = u32Slice(labels_ptr, label_len) catch |err| return setError(err);
    handle.inner.fieldInsertDerivative(field_id, coords, labels, derivative) catch |err| return setError(err);
    handle.frozen = null;
    return 0;
}

/// sc_generated_normal_ordering tags the last count fields as one normal product.
export fn sc_generated_normal_ordering(ctx: ?*Context, count: usize) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    handle.inner.normalOrdering(count) catch |err| return setError(err);
    handle.frozen = null;
    return 0;
}

/// sc_generated_operator_list_freeze freezes the current operator list.
export fn sc_generated_operator_list_freeze(ctx: ?*Context) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    handle.frozen = handle.inner.freeze() catch |err| return setError(err);
    return 0;
}

fn frozen(handle: *Context) !kernel.Call.MultiOp {
    return handle.frozen orelse error.OperatorListNotFrozen;
}

fn operatorCoordinate(op: kernel.Call.LocalOp) u32 {
    return switch (op.insertion) {
        .single => |single| single.position.raw,
        .pair => |pair| pair.holomorphic_position.raw,
    };
}

fn leftCoordinateSlice(ops: kernel.Call.MultiOp, left_count: usize, out: []u32) ![]const u32 {
    if (left_count > ops.operators.len or left_count > out.len) return error.InvalidOpeSplit;
    for (ops.operators[0..left_count], 0..) |op, index| {
        out[index] = operatorCoordinate(op);
    }
    return out[0..left_count];
}

fn rightCoordinate(ops: kernel.Call.MultiOp, left_count: usize) !u32 {
    if (left_count > ops.operators.len) return error.InvalidOpeSplit;
    if (left_count == ops.operators.len) return 0;
    return operatorCoordinate(ops.operators[left_count]);
}

/// sc_generated_correlator_count returns the number of accepted branches.
export fn sc_generated_correlator_count(ctx: ?*Context, out_count: ?*usize) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    const out = out_count orelse return setErrorName("NullOutput");
    const ops = frozen(handle) catch |err| return setError(err);
    out.* = handle.inner.count(ops) catch |err| return setError(err);
    return 0;
}

/// sc_generated_correlator_run streams result events to a callback.
export fn sc_generated_correlator_run(ctx: ?*Context, payload: ?*anyopaque, callback: ?EventCallback) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    const cb = callback orelse return setErrorName("NullCallback");
    const ops = frozen(handle) catch |err| return setError(err);
    var state = StreamState{ .payload = payload, .callback = cb };
    handle.inner.run(ops, &state, streamThunk) catch |err| return setError(err);
    return 0;
}

/// sc_generated_correlator_run_buffered streams bounded event chunks.
export fn sc_generated_correlator_run_buffered(ctx: ?*Context, payload: ?*anyopaque, callback: ?EventChunkCallback) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    const cb = callback orelse return setErrorName("NullCallback");
    const ops = frozen(handle) catch |err| return setError(err);
    var state = BufferedStreamState{ .payload = payload, .callback = cb };
    handle.inner.run(ops, &state, bufferedStreamThunk) catch |err| return setError(err);
    state.flush() catch |err| return setError(err);
    return 0;
}

/// sc_generated_correlator_expression_records returns compact expression terms and factors.
export fn sc_generated_correlator_expression_records(
    ctx: ?*Context,
    out_terms: ?*[*]ExpressionTerm,
    out_term_count: ?*usize,
    out_factors: ?*[*]ExpressionFactor,
    out_factor_count: ?*usize,
    out_names: ?*[*]ExpressionName,
    out_name_count: ?*usize,
) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    const terms_out = out_terms orelse return setErrorName("NullOutput");
    const term_count_out = out_term_count orelse return setErrorName("NullOutput");
    const factors_out = out_factors orelse return setErrorName("NullOutput");
    const factor_count_out = out_factor_count orelse return setErrorName("NullOutput");
    const names_out = out_names orelse return setErrorName("NullOutput");
    const name_count_out = out_name_count orelse return setErrorName("NullOutput");
    const ops = frozen(handle) catch |err| return setError(err);
    var state = ExpressionRecordState{};
    defer state.deinit();
    handle.inner.run(ops, &state, expressionRecordThunk) catch |err| return setError(err);
    const factors = state.factors.toOwnedSlice(allocator) catch |err| return setError(err);
    const terms = state.terms.toOwnedSlice(allocator) catch |err| {
        allocator.free(factors);
        return setError(err);
    };
    const names = state.names.toOwnedSlice(allocator) catch |err| {
        allocator.free(terms);
        allocator.free(factors);
        return setError(err);
    };
    terms_out.* = terms.ptr;
    term_count_out.* = terms.len;
    factors_out.* = factors.ptr;
    factor_count_out.* = factors.len;
    names_out.* = names.ptr;
    name_count_out.* = names.len;
    return 0;
}

/// sc_generated_ope_expression_records returns reusable structured OPE terms.
export fn sc_generated_ope_expression_records(
    ctx: ?*Context,
    left_count: usize,
    target_weight_ticks: i32,
    max_taylor_level: u8,
    out_terms: ?*[*]OpeTerm,
    out_term_count: ?*usize,
    out_factors: ?*[*]OpeFactor,
    out_factor_count: ?*usize,
    out_names: ?*[*]ExpressionName,
    out_name_count: ?*usize,
) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    const terms_out = out_terms orelse return setErrorName("NullOutput");
    const term_count_out = out_term_count orelse return setErrorName("NullOutput");
    const factors_out = out_factors orelse return setErrorName("NullOutput");
    const factor_count_out = out_factor_count orelse return setErrorName("NullOutput");
    const names_out = out_names orelse return setErrorName("NullOutput");
    const name_count_out = out_name_count orelse return setErrorName("NullOutput");
    const ops = frozen(handle) catch |err| return setError(err);
    var left_coords_buffer: [64]u32 = undefined;
    const left_coords = leftCoordinateSlice(ops, left_count, &left_coords_buffer) catch |err| return setError(err);
    var state = OpeRecordState{
        .theory = std.meta.activeTag(handle.inner),
        .left_coords = left_coords,
        .right_coord = rightCoordinate(ops, left_count) catch |err| return setError(err),
    };
    defer state.deinit();
    handle.inner.opeProjected(ops, left_count, .{
        .target_holomorphic_ticks = target_weight_ticks,
        .max_taylor_level = max_taylor_level,
    }, &state) catch |err| return setError(err);
    const factors = state.factors.toOwnedSlice(allocator) catch |err| return setError(err);
    const terms = state.terms.toOwnedSlice(allocator) catch |err| {
        allocator.free(factors);
        return setError(err);
    };
    const names = state.names.toOwnedSlice(allocator) catch |err| {
        allocator.free(terms);
        allocator.free(factors);
        return setError(err);
    };
    terms_out.* = terms.ptr;
    term_count_out.* = terms.len;
    factors_out.* = factors.ptr;
    factor_count_out.* = factors.len;
    names_out.* = names.ptr;
    name_count_out.* = names.len;
    return 0;
}

/// sc_generated_ope_run_buffered streams compact OPE records in bounded chunks.
export fn sc_generated_ope_run_buffered(
    ctx: ?*Context,
    left_count: usize,
    target_weight_ticks: i32,
    max_taylor_level: u8,
    payload: ?*anyopaque,
    callback: ?OpeEventChunkCallback,
) c_int {
    clearError();
    const handle = ctx orelse return setErrorName("NullContext");
    const cb = callback orelse return setErrorName("NullCallback");
    const ops = frozen(handle) catch |err| return setError(err);
    var left_coords_buffer: [64]u32 = undefined;
    const left_coords = leftCoordinateSlice(ops, left_count, &left_coords_buffer) catch |err| return setError(err);
    var state = OpeBufferedStreamState{
        .theory = std.meta.activeTag(handle.inner),
        .left_coords = left_coords,
        .right_coord = rightCoordinate(ops, left_count) catch |err| return setError(err),
        .payload = payload,
        .callback = cb,
    };
    handle.inner.opeProjected(ops, left_count, .{
        .target_holomorphic_ticks = target_weight_ticks,
        .max_taylor_level = max_taylor_level,
    }, &state) catch |err| return setError(err);
    state.flush() catch |err| return setError(err);
    return 0;
}

/// sc_generated_ope_buffer_free releases buffers returned by OPE expression calls.
export fn sc_generated_ope_buffer_free(
    terms: ?[*]OpeTerm,
    term_count: usize,
    factors: ?[*]OpeFactor,
    factor_count: usize,
    names: ?[*]ExpressionName,
    name_count: usize,
) void {
    if (terms) |ptr| allocator.free(ptr[0..term_count]);
    if (factors) |ptr| allocator.free(ptr[0..factor_count]);
    if (names) |ptr| allocator.free(ptr[0..name_count]);
}

/// sc_generated_expression_buffer_free releases compact expression buffers.
export fn sc_generated_expression_buffer_free(
    terms: ?[*]ExpressionTerm,
    term_count: usize,
    factors: ?[*]ExpressionFactor,
    factor_count: usize,
    names: ?[*]ExpressionName,
    name_count: usize,
) void {
    if (terms) |ptr| allocator.free(ptr[0..term_count]);
    if (factors) |ptr| allocator.free(ptr[0..factor_count]);
    if (names) |ptr| allocator.free(ptr[0..name_count]);
}

const AbiEventDigest = struct {
    events: usize = 0,
    scalars: usize = 0,
    coordinates: usize = 0,
    tensors: usize = 0,
    zero_modes: usize = 0,
    saw_green_kernel: bool = false,
    saw_bc_top_form: bool = false,

    fn push(payload: ?*anyopaque, event_ptr: *const Event) callconv(.c) c_int {
        const self: *@This() = @ptrCast(@alignCast(payload.?));
        const event = event_ptr.*;
        self.events += 1;
        switch (@as(descriptor.ResultEventKind, @enumFromInt(event.kind))) {
            .scalar => self.scalars += 1,
            .coordinate => {
                self.coordinates += 1;
                if (event.name_ptr) |ptr| {
                    const name = ptr[0..event.name_len];
                    self.saw_green_kernel = self.saw_green_kernel or std.mem.eql(u8, name, "elliptic_prime_form_log_derivative");
                }
            },
            .tensor => self.tensors += 1,
            .zero_mode => {
                self.zero_modes += 1;
                if (event.name_ptr) |ptr| {
                    const name = ptr[0..event.name_len];
                    self.saw_bc_top_form = self.saw_bc_top_form or std.mem.eql(u8, name, "bc-top-form");
                }
            },
            .sum_term_begin, .sum_term_end, .wick_term_begin, .wick_term_end, .residual_operator => {},
        }
        return 0;
    }
};

const BasisAbiRecorder = struct {
    count: usize = 0,
    saw_base: bool = false,
    saw_named_c_mode: bool = false,

    fn push(payload: ?*anyopaque, record_ptr: *const BasisRecord) callconv(.c) c_int {
        const self: *BasisAbiRecorder = @ptrCast(@alignCast(payload.?));
        const record = record_ptr.*;
        self.count += 1;
        self.saw_base = record.base_weight_ticks == -1 and record.base_quantum_len == 1 and record.base_quantum_ptr.?[0] == 1;
        if (record.mode_len == 1) {
            const mode = record.mode_ptr.?[0];
            self.saw_named_c_mode = mode.name_len == 1 and mode.name_ptr.?[0] == 'c' and mode.weight_ticks == 1;
        }
        return 0;
    }
};

const OpeAbiDigest = struct {
    events: usize = 0,
    term_begin: usize = 0,
    term_end: usize = 0,
    scalars: usize = 0,
    coordinates: usize = 0,
    tensors: usize = 0,
    actions: usize = 0,
    output_fields: usize = 0,
    output_labels: usize = 0,
    saw_branch_level: bool = false,

    fn push(payload: ?*anyopaque, events: [*]const OpeEvent, event_count: usize) callconv(.c) c_int {
        const self: *OpeAbiDigest = @ptrCast(@alignCast(payload.?));
        for (events[0..event_count]) |event| {
            self.events += 1;
            switch (event.kind) {
                OpeFactorKind.term_begin => {
                    self.term_begin += 1;
                    self.saw_branch_level = self.saw_branch_level or event.a != 0;
                },
                OpeFactorKind.term_end => self.term_end += 1,
                OpeFactorKind.scalar_rational, OpeFactorKind.scalar_i, OpeFactorKind.scalar_atom => self.scalars += 1,
                OpeFactorKind.coordinate_difference, OpeFactorKind.coordinate_named, OpeFactorKind.coordinate_exp_green, OpeFactorKind.coordinate_local_power => self.coordinates += 1,
                OpeFactorKind.tensor_metric, OpeFactorKind.tensor_momentum_index, OpeFactorKind.tensor_momentum_pair => self.tensors += 1,
                OpeFactorKind.action_profile_derivative => self.actions += 1,
                OpeFactorKind.output_field => self.output_fields += 1,
                OpeFactorKind.output_label => self.output_labels += 1,
                else => return -1,
            }
        }
        return 0;
    }
};

const OpeDirectCount = struct {
    count: usize = 0,

    pub fn emitOpeTerm(self: *@This(), _: cft_ope.TermView) !void {
        self.count += 1;
    }
};

const NamedBasisModeRecorder = struct {
    expected_name: []const u8,
    count: usize = 0,
    saw_name: bool = false,

    fn push(payload: ?*anyopaque, record_ptr: *const BasisRecord) callconv(.c) c_int {
        const self: *NamedBasisModeRecorder = @ptrCast(@alignCast(payload.?));
        const record = record_ptr.*;
        self.count += 1;
        if (record.mode_len == 0) return 0;
        const mode = record.mode_ptr.?[0];
        if (mode.name_len != self.expected_name.len) return 0;
        const name = mode.name_ptr.?[0..mode.name_len];
        self.saw_name = std.mem.eql(u8, name, self.expected_name);
        return 0;
    }
};

fn expectSymbol(ctx: *Context, name: []const u8) !u32 {
    var symbol: u32 = 0;
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_symbol_intern(ctx, name.ptr, name.len, &symbol));
    return symbol;
}

fn expectInsert(ctx: *Context, field_id: u16, coords: []const u32, labels: []const u32) !void {
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_field_insert(
        ctx,
        field_id,
        if (coords.len == 0) null else coords.ptr,
        coords.len,
        if (labels.len == 0) null else labels.ptr,
        labels.len,
    ));
}

fn expectInsertDerivative(ctx: *Context, field_id: u16, coords: []const u32, labels: []const u32, derivative: u8) !void {
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_field_insert_derivative(
        ctx,
        field_id,
        if (coords.len == 0) null else coords.ptr,
        coords.len,
        if (labels.len == 0) null else labels.ptr,
        labels.len,
        derivative,
    ));
}

fn expectFrozenDigest(ctx: *Context, expected_count: usize) !AbiEventDigest {
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_operator_list_freeze(ctx));

    var count: usize = 0;
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_correlator_count(ctx, &count));
    try std.testing.expectEqual(expected_count, count);

    var digest = AbiEventDigest{};
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_correlator_run(ctx, &digest, AbiEventDigest.push));
    try std.testing.expect(digest.events > 0);
    return digest;
}

fn expectExpressionRecords(ctx: *Context, expected_terms: usize, min_factors: usize, min_names: usize) !void {
    var terms: [*]ExpressionTerm = undefined;
    var term_count: usize = 0;
    var factors: [*]ExpressionFactor = undefined;
    var factor_count: usize = 0;
    var names: [*]ExpressionName = undefined;
    var name_count: usize = 0;
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_correlator_expression_records(
        ctx,
        &terms,
        &term_count,
        &factors,
        &factor_count,
        &names,
        &name_count,
    ));
    defer sc_generated_expression_buffer_free(terms, term_count, factors, factor_count, names, name_count);

    try std.testing.expectEqual(expected_terms, term_count);
    try std.testing.expect(factor_count >= min_factors);
    try std.testing.expect(name_count >= min_names);
    for (terms[0..term_count]) |term| {
        try std.testing.expect(term.first_factor <= factor_count);
        try std.testing.expect(term.first_factor + term.factor_count <= factor_count);
    }
}

fn expectOpeExpressionRecords(ctx: *Context, left_count: usize, expected_terms: usize, min_factors: usize) !void {
    var terms: [*]OpeTerm = undefined;
    var term_count: usize = 0;
    var factors: [*]OpeFactor = undefined;
    var factor_count: usize = 0;
    var names: [*]ExpressionName = undefined;
    var name_count: usize = 0;
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_ope_expression_records(
        ctx,
        left_count,
        0,
        0,
        &terms,
        &term_count,
        &factors,
        &factor_count,
        &names,
        &name_count,
    ));
    defer sc_generated_ope_buffer_free(terms, term_count, factors, factor_count, names, name_count);

    try std.testing.expectEqual(expected_terms, term_count);
    try std.testing.expect(factor_count >= min_factors);
    for (terms[0..term_count]) |term| {
        try std.testing.expect(term.first_factor <= factor_count);
        try std.testing.expect(term.first_factor + term.factor_count <= factor_count);
    }
}

fn expectDirectOpeCount(ctx: *Context, left_count: usize, expected_terms: usize) !void {
    const ops = try frozen(ctx);
    var sink = OpeDirectCount{};
    try ctx.inner.opeProjected(ops, left_count, .{
        .target_holomorphic_ticks = 0,
        .max_taylor_level = 0,
    }, &sink);
    try std.testing.expectEqual(expected_terms, sink.count);
}

fn expectOpeStream(ctx: *Context, left_count: usize, expected_terms: usize, min_factors: usize, expected: struct {
    coordinates: bool = false,
    tensors: bool = false,
    outputs: bool = false,
    output_labels: bool = false,
}) !void {
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_operator_list_freeze(ctx));

    var digest = OpeAbiDigest{};
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_ope_run_buffered(
        ctx,
        left_count,
        0,
        0,
        &digest,
        OpeAbiDigest.push,
    ));
    try std.testing.expectEqual(expected_terms, digest.term_begin);
    try std.testing.expectEqual(expected_terms, digest.term_end);
    try std.testing.expect(digest.events >= expected_terms * 2 + min_factors);
    if (expected.outputs) {
        try std.testing.expect(digest.output_fields > 0);
    }
    if (expected.coordinates) try std.testing.expect(digest.coordinates > 0);
    if (expected.tensors) try std.testing.expect(digest.tensors > 0);
    if (expected.output_labels) try std.testing.expect(digest.output_labels > 0);

    try expectOpeExpressionRecords(ctx, left_count, expected_terms, min_factors);
    try expectDirectOpeCount(ctx, left_count, expected_terms);
}

fn expectFreeFermionAbiStream() !void {
    const ctx = sc_generated_context_create(@intFromEnum(TheoryId.free_fermion)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    const mu = try expectSymbol(ctx, "mu");
    const nu = try expectSymbol(ctx, "nu");
    const z = try expectSymbol(ctx, "z");
    const w = try expectSymbol(ctx, "w");
    try expectInsert(ctx, 0, &.{z}, &.{mu});
    try expectInsert(ctx, 0, &.{w}, &.{nu});

    const digest = try expectFrozenDigest(ctx, 1);
    try std.testing.expect(digest.coordinates >= 1);
    try std.testing.expect(digest.tensors >= 1);
    try std.testing.expectEqual(@as(usize, 0), digest.zero_modes);
    try expectExpressionRecords(ctx, 1, 2, 1);
}

fn expectEtaXiSphereAbiStream() !void {
    const ctx = sc_generated_context_create(@intFromEnum(TheoryId.eta_xi_sphere)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    const z = try expectSymbol(ctx, "z");
    const w = try expectSymbol(ctx, "w");
    try expectInsert(ctx, 0, &.{z}, &.{});
    try expectInsert(ctx, 1, &.{w}, &.{});

    const digest = try expectFrozenDigest(ctx, 1);
    try std.testing.expect(digest.coordinates >= 1);
    try std.testing.expectEqual(@as(usize, 0), digest.zero_modes);
    try expectExpressionRecords(ctx, 1, 1, 0);
}

fn expectEtaXiTorusAbiStream() !void {
    const ctx = sc_generated_context_create(@intFromEnum(TheoryId.eta_xi_torus)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    const z = try expectSymbol(ctx, "z");
    const w = try expectSymbol(ctx, "w");
    try expectInsert(ctx, 0, &.{z}, &.{});
    try expectInsert(ctx, 1, &.{w}, &.{});

    const digest = try expectFrozenDigest(ctx, 1);
    try std.testing.expect(digest.coordinates >= 1);
    try std.testing.expect(digest.saw_green_kernel);
    try expectExpressionRecords(ctx, 1, 1, 1);
}

fn expectBcAbiStream() !void {
    const ctx = sc_generated_context_create(@intFromEnum(TheoryId.bc)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    const z1 = try expectSymbol(ctx, "z1");
    const z2 = try expectSymbol(ctx, "z2");
    const z3 = try expectSymbol(ctx, "z3");
    try expectInsert(ctx, 1, &.{z1}, &.{});
    try expectInsert(ctx, 1, &.{z2}, &.{});
    try expectInsert(ctx, 1, &.{z3}, &.{});

    const digest = try expectFrozenDigest(ctx, 1);
    try std.testing.expect(digest.zero_modes >= 1);
    try std.testing.expect(digest.saw_bc_top_form);
    try expectExpressionRecords(ctx, 1, 1, 1);
}

fn expectFreeBosonAbiStream() !void {
    const ctx = sc_generated_context_create(@intFromEnum(TheoryId.free_boson)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    const mu = try expectSymbol(ctx, "mu");
    const nu = try expectSymbol(ctx, "nu");
    const z = try expectSymbol(ctx, "z");
    const w = try expectSymbol(ctx, "w");
    try expectInsert(ctx, 1, &.{z}, &.{mu});
    try expectInsert(ctx, 1, &.{w}, &.{nu});

    const digest = try expectFrozenDigest(ctx, 1);
    try std.testing.expect(digest.scalars >= 1);
    try std.testing.expect(digest.coordinates >= 1);
    try std.testing.expect(digest.tensors >= 1);
    try expectExpressionRecords(ctx, 1, 3, 3);
}

fn expectBcOpeAbi() !void {
    const ctx = sc_generated_context_create(@intFromEnum(TheoryId.bc)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    const z = try expectSymbol(ctx, "z");
    const w = try expectSymbol(ctx, "w");
    try expectInsert(ctx, 0, &.{z}, &.{});
    try expectInsert(ctx, 1, &.{w}, &.{});

    try expectOpeStream(ctx, 1, 1, 1, .{ .coordinates = true });

    var digest = OpeAbiDigest{};
    try std.testing.expectEqual(@as(c_int, -1), sc_generated_ope_run_buffered(ctx, 3, 0, 0, &digest, OpeAbiDigest.push));
    try std.testing.expect(std.mem.eql(u8, std.mem.span(sc_generated_last_error()), "InvalidOpeSplit"));
}

fn expectFreeFermionOpeAbi() !void {
    const ctx = sc_generated_context_create(@intFromEnum(TheoryId.free_fermion)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    const mu = try expectSymbol(ctx, "mu");
    const z = try expectSymbol(ctx, "z");
    const w = try expectSymbol(ctx, "w");
    try expectInsert(ctx, 0, &.{z}, &.{mu});
    try expectInsert(ctx, 0, &.{w}, &.{mu});

    try expectOpeStream(ctx, 1, 1, 2, .{ .coordinates = true, .tensors = true });
}

fn expectFreeBosonDerivativeOpeAbi() !void {
    const ctx = sc_generated_context_create(@intFromEnum(TheoryId.free_boson)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    const mu = try expectSymbol(ctx, "mu");
    const nu = try expectSymbol(ctx, "nu");
    const z = try expectSymbol(ctx, "z");
    const w = try expectSymbol(ctx, "w");
    try expectInsertDerivative(ctx, 1, &.{z}, &.{mu}, 1);
    try expectInsertDerivative(ctx, 1, &.{w}, &.{nu}, 3);

    try expectOpeStream(ctx, 1, 1, 3, .{ .coordinates = true, .tensors = true });
}

fn expectFreeBosonExpOpeAbi() !void {
    const ctx = sc_generated_context_create(@intFromEnum(TheoryId.free_boson)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    const k = try expectSymbol(ctx, "k");
    const p = try expectSymbol(ctx, "p");
    const z = try expectSymbol(ctx, "z");
    const zb = try expectSymbol(ctx, "zb");
    const w = try expectSymbol(ctx, "w");
    const wb = try expectSymbol(ctx, "wb");
    try expectInsert(ctx, 3, &.{ z, zb }, &.{k});
    try expectInsert(ctx, 3, &.{ w, wb }, &.{p});

    try expectOpeStream(ctx, 1, 1, 5, .{ .coordinates = true, .tensors = true, .outputs = true, .output_labels = true });
}

fn expectGeneratedOpeAbi() !void {
    try expectBcOpeAbi();
    try expectFreeFermionOpeAbi();
    try expectFreeBosonDerivativeOpeAbi();
    try expectFreeBosonExpOpeAbi();
}

fn expectGeneratedCorrelatorStreams() !void {
    try expectFreeFermionAbiStream();
    try expectEtaXiSphereAbiStream();
    try expectEtaXiTorusAbiStream();
    try expectBcAbiStream();
    try expectFreeBosonAbiStream();
}

fn expectBasisCount(raw_theory: u32, weight_kind: u8, weight_ticks: i32, max_depth: u16, filters: []const BasisQuantumFilter, expected: usize) !void {
    return expectBasisCountLevel(raw_theory, weight_kind, weight_ticks, max_depth, 0, filters, expected);
}

fn expectBasisCountLevel(raw_theory: u32, weight_kind: u8, weight_ticks: i32, max_depth: u16, level_match: u8, filters: []const BasisQuantumFilter, expected: usize) !void {
    var count: usize = 0;
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_basis_count(
        raw_theory,
        weight_kind,
        weight_ticks,
        max_depth,
        level_match,
        if (filters.len == 0) null else filters.ptr,
        filters.len,
        &count,
    ));
    try std.testing.expectEqual(expected, count);
}

fn expectGeneratedMetadataMatchesDispatch() !void {
    inline for (std.meta.fields(TheoryId)) |field| {
        const raw_theory: u32 = field.value;
        const id: TheoryId = @enumFromInt(raw_theory);
        try std.testing.expectEqual(dispatch.theoryHash(id), sc_generated_theory_hash(raw_theory));

        var field_id: u16 = 0;
        var seen: usize = 0;
        while (true) : (field_id += 1) {
            var name_ptr: ?[*]const u8 = null;
            var name_len: usize = 0;
            var coordinate_arity: usize = 0;
            var label_arity: usize = 0;
            const result = sc_generated_field_metadata(
                raw_theory,
                field_id,
                &name_ptr,
                &name_len,
                &coordinate_arity,
                &label_arity,
            );
            const expected_name = dispatch.fieldName(id, field_id) orelse {
                try std.testing.expectEqual(@as(c_int, -1), result);
                try std.testing.expect(std.mem.startsWith(u8, std.mem.span(sc_generated_last_error()), "UnknownField id="));
                break;
            };
            try std.testing.expectEqual(@as(c_int, 0), result);
            try std.testing.expect(std.mem.eql(u8, name_ptr.?[0..name_len], expected_name));
            try std.testing.expectEqual(dispatch.fieldCoordinateArity(id, field_id).?, coordinate_arity);
            try std.testing.expectEqual(dispatch.fieldLabelArity(id, field_id).?, label_arity);
            seen += 1;
        }
        try std.testing.expect(seen > 0);
    }
}

fn expectGeneratedAbiFailurePaths() !void {
    try std.testing.expectEqual(@as(?*Context, null), sc_generated_context_create(999_999));
    try std.testing.expect(std.mem.eql(u8, std.mem.span(sc_generated_last_error()), "UnknownTheory"));

    const ctx = sc_generated_context_create(@intFromEnum(dispatch.first_theory_id)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    var terms: [*]ExpressionTerm = undefined;
    var term_count: usize = 0;
    var factors: [*]ExpressionFactor = undefined;
    var factor_count: usize = 0;
    var names: [*]ExpressionName = undefined;
    var name_count: usize = 0;
    try std.testing.expectEqual(@as(c_int, -1), sc_generated_correlator_expression_records(
        ctx,
        &terms,
        &term_count,
        &factors,
        &factor_count,
        &names,
        &name_count,
    ));
    try std.testing.expect(std.mem.eql(u8, std.mem.span(sc_generated_last_error()), "OperatorListNotFrozen"));

    var basis_count: usize = 0;
    try std.testing.expectEqual(@as(c_int, -1), sc_generated_basis_count(
        @intFromEnum(dispatch.first_theory_id),
        2,
        0,
        0,
        0,
        null,
        0,
        &basis_count,
    ));
    try std.testing.expect(std.mem.eql(u8, std.mem.span(sc_generated_last_error()), "InvalidQuery"));
}

test "generated C ABI matches descriptor dispatch metadata and streams events" {
    try selfTest();
}

/// selfTest runs the generated C ABI fixture invariants.
pub fn selfTest() !void {
    try expectGeneratedMetadataMatchesDispatch();
    try expectGeneratedCorrelatorStreams();
    try expectGeneratedOpeAbi();
    try expectGeneratedAbiFailurePaths();

    const ctx = sc_generated_context_create(@intFromEnum(dispatch.first_theory_id)) orelse return error.ContextCreateFailed;
    defer sc_generated_context_destroy(ctx);

    var mu: u32 = 0;
    var nu: u32 = 0;
    var z: u32 = 0;
    var w: u32 = 0;
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_symbol_intern(ctx, "mu".ptr, 2, &mu));
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_symbol_intern(ctx, "nu".ptr, 2, &nu));
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_symbol_intern(ctx, "z".ptr, 1, &z));
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_symbol_intern(ctx, "w".ptr, 1, &w));

    var field_name_ptr: ?[*]const u8 = null;
    var field_name_len: usize = 0;
    var field_coord_arity: usize = 0;
    var field_label_arity: usize = 0;
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_field_metadata(
        @intFromEnum(dispatch.first_theory_id),
        0,
        &field_name_ptr,
        &field_name_len,
        &field_coord_arity,
        &field_label_arity,
    ));
    try std.testing.expect(std.mem.eql(u8, field_name_ptr.?[0..field_name_len], "psi"));
    try std.testing.expectEqual(@as(usize, 1), field_coord_arity);
    try std.testing.expectEqual(@as(usize, 1), field_label_arity);

    try std.testing.expectEqual(@as(c_int, 0), sc_generated_field_insert(ctx, 0, &.{z}, 1, &.{mu}, 1));
    try std.testing.expectEqual(@as(c_int, -1), sc_generated_field_insert(ctx, 0, &.{z}, 1, &.{}, 0));
    try std.testing.expect(std.mem.eql(u8, std.mem.span(sc_generated_last_error()), "Field psi expects 1 labels, got 0"));
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_field_insert(ctx, 0, &.{w}, 1, &.{nu}, 1));
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_operator_list_freeze(ctx));

    var count: usize = 0;
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_correlator_count(ctx, &count));
    try std.testing.expectEqual(@as(usize, 1), count);

    const filters = [_]BasisQuantumFilter{.{ .slot = 0, .value = 0 }};
    var basis_count: usize = 0;
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_basis_count(
        @intFromEnum(TheoryId.bc),
        0,
        0,
        1,
        0,
        &filters,
        filters.len,
        &basis_count,
    ));
    try std.testing.expectEqual(@as(usize, 1), basis_count);

    var basis_recorder = BasisAbiRecorder{};
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_basis_run_compact(
        @intFromEnum(TheoryId.bc),
        0,
        0,
        1,
        0,
        &filters,
        filters.len,
        &basis_recorder,
        BasisAbiRecorder.push,
    ));
    try std.testing.expectEqual(@as(usize, 1), basis_recorder.count);
    try std.testing.expect(basis_recorder.saw_base);
    try std.testing.expect(basis_recorder.saw_named_c_mode);

    var text_ptr: ?[*]u8 = null;
    var text_len: usize = 0;
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_basis_text(
        @intFromEnum(TheoryId.bc),
        0,
        0,
        1,
        0,
        &filters,
        filters.len,
        2,
        8,
        &text_ptr,
        &text_len,
    ));
    defer sc_generated_basis_text_free(text_ptr, text_len);
    try std.testing.expect(std.mem.indexOf(u8, text_ptr.?[0..text_len], ":c(0) d^2c(0):") != null);

    const eta_xi_filters = [_]BasisQuantumFilter{.{ .slot = 0, .value = -1 }};
    try expectBasisCount(@intFromEnum(TheoryId.eta_xi_sphere), 0, 0, 0, &eta_xi_filters, 1);
    try expectBasisCount(@intFromEnum(TheoryId.eta_xi_torus), 0, 0, 0, &eta_xi_filters, 1);

    try expectBasisCount(@intFromEnum(TheoryId.free_boson), 0, 2, 2, &.{}, 65);

    const fermion_filters = [_]BasisQuantumFilter{.{ .slot = 0, .value = 1 }};
    try expectBasisCount(@intFromEnum(TheoryId.free_fermion), 0, 1, 1, &fermion_filters, 10);
    var fermion_recorder = NamedBasisModeRecorder{ .expected_name = "psi" };
    try std.testing.expectEqual(@as(c_int, 0), sc_generated_basis_run_compact(
        @intFromEnum(TheoryId.free_fermion),
        0,
        1,
        1,
        0,
        &fermion_filters,
        fermion_filters.len,
        &fermion_recorder,
        NamedBasisModeRecorder.push,
    ));
    try std.testing.expectEqual(@as(usize, 10), fermion_recorder.count);
    try std.testing.expect(fermion_recorder.saw_name);

    try expectBasisCountLevel(basisProductPairId(@intFromEnum(TheoryId.free_boson), @intFromEnum(TheoryId.free_boson)), 0, 2, 2, 1, &.{}, 100);
    try expectBasisCountLevel(basisProductPairId(@intFromEnum(TheoryId.bc), @intFromEnum(TheoryId.free_boson)), 0, 0, 1, 0, &.{.{ .slot = 0, .value = 0 }}, 1);
}
