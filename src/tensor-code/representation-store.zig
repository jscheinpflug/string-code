const std = @import("std");
const root_data = @import("root-data.zig");
const symmetry = @import("symmetry.zig");

/// AlgebraHandle names a registered Lie algebra in a tensor context.
pub const AlgebraHandle = struct {
    value: u32,

    /// init constructs an algebra handle from a store index.
    pub fn init(value: u32) AlgebraHandle {
        return .{ .value = value };
    }
};

/// IrrepHandle names an abstract irreducible representation.
pub const IrrepHandle = struct {
    value: u32,

    /// init constructs an irrep handle from a store index.
    pub fn init(value: u32) IrrepHandle {
        return .{ .value = value };
    }
};

/// ChannelHandle names one irrep copy inside a local product.
pub const ChannelHandle = struct {
    value: u32,

    /// init constructs a channel handle from a store index.
    pub fn init(value: u32) ChannelHandle {
        return .{ .value = value };
    }
};

/// AlgebraSpec describes a requested algebra before it is interned.
pub const AlgebraSpec = union(enum) {
    u1,
    simple: symmetry.SimpleLieAlgebra,
};

/// IrrepSpec describes a requested representation before it is interned.
pub const IrrepSpec = union(enum) {
    u1_charge: symmetry.U1ChargeRational,
    dynkin: []const i16,
};

/// IrrepMetadata stores derived representation data.
pub const IrrepMetadata = struct {
    dimension: ?u128 = null,
    dual: ?IrrepHandle = null,
    quadratic_casimir: ?root_data.Rational = null,
};

/// Store owns interned algebra and irrep records.
pub const Store = struct {
    allocator: std.mem.Allocator,
    conventions: root_data.AlgebraConventions,
    algebras: std.ArrayList(AlgebraRecord) = .empty,
    irreps: std.ArrayList(IrrepRecord) = .empty,

    /// init constructs an empty representation store.
    pub fn init(allocator: std.mem.Allocator, conventions: root_data.AlgebraConventions) Store {
        return .{ .allocator = allocator, .conventions = conventions };
    }

    /// deinit releases all representation-store memory.
    pub fn deinit(self: *Store) void {
        for (self.irreps.items) |record| {
            switch (record.label) {
                .dynkin => |label| self.allocator.free(label),
                .u1_charge => {},
            }
        }
        self.irreps.deinit(self.allocator);
        self.algebras.deinit(self.allocator);
        self.* = Store.init(self.allocator, self.conventions);
    }

    /// internAlgebra returns the stable handle for an algebra spec.
    pub fn internAlgebra(self: *Store, spec: AlgebraSpec) !AlgebraHandle {
        try validateAlgebraSpec(spec);
        for (self.algebras.items, 0..) |record, index| {
            if (algebraSpecEql(record.spec, spec)) {
                return AlgebraHandle.init(@intCast(index));
            }
        }

        try self.algebras.append(self.allocator, .{
            .spec = spec,
            .root_data = try makeRootDatum(spec, self.conventions),
        });
        return AlgebraHandle.init(@intCast(self.algebras.items.len - 1));
    }

    /// containsAlgebra returns whether an algebra handle belongs to this store.
    pub fn containsAlgebra(self: Store, handle: AlgebraHandle) bool {
        return self.algebraRecord(handle) != null;
    }

    /// internIrrep returns the stable handle for an irrep spec in an algebra.
    pub fn internIrrep(self: *Store, algebra: AlgebraHandle, spec: IrrepSpec) anyerror!IrrepHandle {
        const algebra_record = self.algebraRecord(algebra) orelse return error.UnknownAlgebra;
        try validateIrrepSpec(algebra_record.spec, spec);

        for (self.irreps.items, 0..) |record, index| {
            if (handleEql(record.algebra, algebra) and irrepLabelSpecEql(record.label, spec)) {
                return IrrepHandle.init(@intCast(index));
            }
        }

        const label = try cloneIrrepSpec(self.allocator, spec);
        errdefer freeIrrepLabel(self.allocator, label);

        try self.irreps.append(self.allocator, .{
            .algebra = algebra,
            .label = label,
            .metadata = .{},
        });
        errdefer _ = self.irreps.pop();
        const handle = IrrepHandle.init(@intCast(self.irreps.items.len - 1));
        try self.fillIrrepMetadata(handle);
        return handle;
    }

    /// dualIrrep returns the handle for the dual irrep, interning it if requested.
    pub fn dualIrrep(self: *Store, handle: IrrepHandle) anyerror!IrrepHandle {
        const index: usize = @intCast(handle.value);
        if (index >= self.irreps.items.len) return error.UnknownIrrep;
        if (self.irreps.items[index].metadata.dual) |dual| return dual;

        const record = self.irreps.items[index];
        const dual = switch (record.label) {
            .u1_charge => |charge| try self.internIrrep(record.algebra, .{ .u1_charge = .{
                .numerator = -charge.numerator,
                .denominator = charge.denominator,
            } }),
            .dynkin => |label| dual: {
                const algebra = self.algebraRecord(record.algebra) orelse return error.UnknownAlgebra;
                const dual_label = try root_data.dualDynkin(self.allocator, algebra.spec.simple, label);
                defer self.allocator.free(dual_label);
                break :dual try self.internIrrep(record.algebra, .{ .dynkin = dual_label });
            },
        };

        self.irreps.items[index].metadata.dual = dual;
        const dual_index: usize = @intCast(dual.value);
        if (dual_index < self.irreps.items.len) self.irreps.items[dual_index].metadata.dual = handle;
        return dual;
    }

    /// containsIrrep returns whether an irrep handle belongs to this store.
    pub fn containsIrrep(self: Store, handle: IrrepHandle) bool {
        return self.irrepRecord(handle) != null;
    }

    /// irrepMetadata returns derived metadata for an irrep handle.
    pub fn irrepMetadata(self: Store, handle: IrrepHandle) ?IrrepMetadata {
        const record = self.irrepRecord(handle) orelse return null;
        return record.metadata;
    }

    /// irrepAlgebra returns the algebra that owns an irrep handle.
    pub fn irrepAlgebra(self: Store, handle: IrrepHandle) ?AlgebraHandle {
        const record = self.irrepRecord(handle) orelse return null;
        return record.algebra;
    }

    fn algebraRecord(self: Store, handle: AlgebraHandle) ?AlgebraRecord {
        const index: usize = @intCast(handle.value);
        if (index >= self.algebras.items.len) return null;
        return self.algebras.items[index];
    }

    fn irrepRecord(self: Store, handle: IrrepHandle) ?IrrepRecord {
        const index: usize = @intCast(handle.value);
        if (index >= self.irreps.items.len) return null;
        return self.irreps.items[index];
    }

    fn fillIrrepMetadata(self: *Store, handle: IrrepHandle) anyerror!void {
        const index: usize = @intCast(handle.value);
        const record = self.irreps.items[index];
        const algebra = self.algebraRecord(record.algebra) orelse return error.UnknownAlgebra;

        switch (record.label) {
            .u1_charge => |charge| {
                self.irreps.items[index].metadata.dimension = 1;
                self.irreps.items[index].metadata.quadratic_casimir = try u1QuadraticCasimir(charge);
                if (charge.numerator == 0) self.irreps.items[index].metadata.dual = handle;
            },
            .dynkin => |label| {
                const simple = algebra.spec.simple;
                self.irreps.items[index].metadata.dimension = try root_data.dimension(self.allocator, simple, label);
                self.irreps.items[index].metadata.quadratic_casimir = try root_data.quadraticCasimir(self.allocator, simple, label, self.conventions);
                const dual_label = try root_data.dualDynkin(self.allocator, simple, label);
                defer self.allocator.free(dual_label);
                if (std.mem.eql(i16, label, dual_label)) {
                    self.irreps.items[index].metadata.dual = handle;
                } else if (self.findIrrep(record.algebra, .{ .dynkin = dual_label })) |dual| {
                    self.irreps.items[index].metadata.dual = dual;
                }
            },
        }
    }

    fn findIrrep(self: Store, algebra: AlgebraHandle, spec: IrrepSpec) ?IrrepHandle {
        for (self.irreps.items, 0..) |record, index| {
            if (handleEql(record.algebra, algebra) and irrepLabelSpecEql(record.label, spec)) {
                return IrrepHandle.init(@intCast(index));
            }
        }
        return null;
    }
};

const AlgebraRecord = struct {
    spec: AlgebraSpec,
    root_data: ?root_data.RootDatum,
};

const IrrepRecord = struct {
    algebra: AlgebraHandle,
    label: IrrepLabel,
    metadata: IrrepMetadata,
};

const IrrepLabel = union(enum) {
    u1_charge: symmetry.U1ChargeRational,
    dynkin: []const i16,
};

const ChannelRecord = struct {
    irrep: IrrepHandle,
    multiplicity_copy: u16,
};

const OccurrenceKind = enum {
    external_leg,
    product_node,
    realization,
};

const OccurrenceRecord = struct {
    channel: ChannelHandle,
    kind: OccurrenceKind,
    source_id: u32,
    realization: ?u32 = null,
};

fn handleEql(left: AlgebraHandle, right: AlgebraHandle) bool {
    return left.value == right.value;
}

fn validateAlgebraSpec(spec: AlgebraSpec) !void {
    switch (spec) {
        .u1 => {},
        .simple => |simple| try root_data.validateSimple(simple),
    }
}

fn makeRootDatum(spec: AlgebraSpec, conventions: root_data.AlgebraConventions) !?root_data.RootDatum {
    return switch (spec) {
        .u1 => null,
        .simple => |simple| try root_data.RootDatum.init(simple, conventions),
    };
}

fn algebraSpecEql(left: AlgebraSpec, right: AlgebraSpec) bool {
    return switch (left) {
        .u1 => switch (right) {
            .u1 => true,
            .simple => false,
        },
        .simple => |left_simple| switch (right) {
            .u1 => false,
            .simple => |right_simple| left_simple.family == right_simple.family and left_simple.rank == right_simple.rank,
        },
    };
}

fn validateIrrepSpec(algebra: AlgebraSpec, spec: IrrepSpec) !void {
    switch (algebra) {
        .u1 => switch (spec) {
            .u1_charge => |charge| {
                if (charge.denominator == 0) return error.InvalidU1Charge;
            },
            .dynkin => return error.InvalidIrrepForAlgebra,
        },
        .simple => |simple| switch (spec) {
            .u1_charge => return error.InvalidIrrepForAlgebra,
            .dynkin => |label| {
                if (label.len != simple.rank) return error.InvalidDynkinRank;
                for (label) |entry| {
                    if (entry < 0) return error.InvalidDynkinLabel;
                }
            },
        },
    }
}

fn u1QuadraticCasimir(charge: symmetry.U1ChargeRational) !root_data.Rational {
    const numerator = @as(i128, charge.numerator) * @as(i128, charge.numerator);
    const denominator = @as(i128, charge.denominator) * @as(i128, charge.denominator);
    return root_data.Rational.init(numerator, denominator);
}

fn irrepLabelSpecEql(left: IrrepLabel, right: IrrepSpec) bool {
    return switch (left) {
        .u1_charge => |left_charge| switch (right) {
            .u1_charge => |right_charge| left_charge.numerator == right_charge.numerator and left_charge.denominator == right_charge.denominator,
            .dynkin => false,
        },
        .dynkin => |left_dynkin| switch (right) {
            .u1_charge => false,
            .dynkin => |right_dynkin| std.mem.eql(i16, left_dynkin, right_dynkin),
        },
    };
}

fn cloneIrrepSpec(allocator: std.mem.Allocator, spec: IrrepSpec) !IrrepLabel {
    return switch (spec) {
        .u1_charge => |charge| .{ .u1_charge = charge },
        .dynkin => |label| .{ .dynkin = try allocator.dupe(i16, label) },
    };
}

fn freeIrrepLabel(allocator: std.mem.Allocator, label: IrrepLabel) void {
    switch (label) {
        .dynkin => |dynkin| allocator.free(dynkin),
        .u1_charge => {},
    }
}
