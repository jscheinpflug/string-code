const std = @import("std");
const projector = @import("projector.zig");
const realization = @import("realization.zig");
const store = @import("representation-store.zig");

/// BasisHandle names a generated invariant basis.
pub const BasisHandle = struct {
    value: u32,

    /// init constructs a basis handle from a store index.
    pub fn init(value: u32) BasisHandle {
        return .{ .value = value };
    }
};

/// InvariantHandle names one invariant inside a basis.
pub const InvariantHandle = struct {
    value: u32,

    /// init constructs an invariant handle from a store index.
    pub fn init(value: u32) InvariantHandle {
        return .{ .value = value };
    }
};

/// TargetIrrep selects the target representation, usually the singlet.
pub const TargetIrrep = union(enum) {
    singlet,
    irrep: store.IrrepHandle,
};

/// TreePolicy controls the coupling tree used for a basis.
pub const TreePolicy = union(enum) {
    auto,
    fixed: []const u16,
};

/// BasisPolicy controls the public basis convention.
pub const BasisPolicy = enum {
    default,
    coupling_paths,
    channel_adapted,
};

/// InvariantBasisRequest is the CFT-facing request for invariant tensors.
pub const InvariantBasisRequest = struct {
    algebra: store.AlgebraHandle,
    external_legs: []const realization.ExternalLeg,
    target: TargetIrrep = .singlet,
    tree_policy: TreePolicy = .auto,
    basis_policy: BasisPolicy = .default,
};

/// TensorExpansionTerm stores a CFT coefficient attached to one invariant id.
pub const TensorExpansionTerm = struct {
    rational_function_id: u32,
    invariant: InvariantHandle,
    scalar_id: u32,
};

/// Store owns interned invariant-basis requests.
pub const Store = struct {
    allocator: std.mem.Allocator,
    requests: std.ArrayList(InvariantBasisRequest) = .empty,

    /// init constructs an empty coupling store.
    pub fn init(allocator: std.mem.Allocator) Store {
        return .{ .allocator = allocator };
    }

    /// deinit releases all coupling-store memory.
    pub fn deinit(self: *Store) void {
        for (self.requests.items) |request| {
            freeRequest(self.allocator, request);
        }
        self.requests.deinit(self.allocator);
        self.* = Store.init(self.allocator);
    }

    /// internBasisRequest returns a stable basis handle for a request.
    pub fn internBasisRequest(self: *Store, request: InvariantBasisRequest) !BasisHandle {
        for (self.requests.items, 0..) |stored, index| {
            if (requestEql(stored, request)) {
                return BasisHandle.init(@intCast(index));
            }
        }

        const owned = try cloneRequest(self.allocator, request);
        errdefer freeRequest(self.allocator, owned);
        try self.requests.append(self.allocator, owned);
        return BasisHandle.init(@intCast(self.requests.items.len - 1));
    }
};

/// CouplingInput names either an external leg or a previous coupling node.
const CouplingInput = union(enum) {
    external: realization.ExternalLegHandle,
    node: u32,
};

/// CouplingNodeRecord stores one binary coupling step.
const CouplingNodeRecord = struct {
    left: CouplingInput,
    right: CouplingInput,
    output: store.ChannelHandle,
    kernel: projector.ProjectorId,
};

/// CouplingPathRecord stores a compact invariant basis element.
const CouplingPathRecord = struct {
    external_offset: u32,
    external_len: u16,
    node_offset: u32,
    node_len: u16,
};

/// BasisRecord stores one generated invariant basis.
const BasisRecord = struct {
    request: InvariantBasisRequest,
    path_offset: u32,
    path_len: u32,
};

/// ReachabilityRecord stores pruning data for one coupling tree node.
const ReachabilityRecord = struct {
    node: u32,
    irrep_offset: u32,
    irrep_len: u32,
};

fn requestEql(left: InvariantBasisRequest, right: InvariantBasisRequest) bool {
    return left.algebra.value == right.algebra.value and
        targetEql(left.target, right.target) and
        treePolicyEql(left.tree_policy, right.tree_policy) and
        left.basis_policy == right.basis_policy and
        externalLegsEql(left.external_legs, right.external_legs);
}

fn targetEql(left: TargetIrrep, right: TargetIrrep) bool {
    return switch (left) {
        .singlet => switch (right) {
            .singlet => true,
            .irrep => false,
        },
        .irrep => |left_irrep| switch (right) {
            .singlet => false,
            .irrep => |right_irrep| left_irrep.value == right_irrep.value,
        },
    };
}

fn treePolicyEql(left: TreePolicy, right: TreePolicy) bool {
    return switch (left) {
        .auto => switch (right) {
            .auto => true,
            .fixed => false,
        },
        .fixed => |left_fixed| switch (right) {
            .auto => false,
            .fixed => |right_fixed| std.mem.eql(u16, left_fixed, right_fixed),
        },
    };
}

fn externalLegsEql(left: []const realization.ExternalLeg, right: []const realization.ExternalLeg) bool {
    if (left.len != right.len) return false;
    for (left, right) |left_leg, right_leg| {
        if (!externalLegEql(left_leg, right_leg)) return false;
    }
    return true;
}

fn externalLegEql(left: realization.ExternalLeg, right: realization.ExternalLeg) bool {
    return realizationRefEql(left.realization, right.realization) and
        namedIndicesEql(left.indices, right.indices) and
        optionalStringEql(left.label, right.label);
}

fn realizationRefEql(left: realization.RealizationRef, right: realization.RealizationRef) bool {
    return switch (left) {
        .primitive_irrep => |left_irrep| switch (right) {
            .primitive_irrep => |right_irrep| left_irrep.value == right_irrep.value,
            else => false,
        },
        .handle => |left_handle| switch (right) {
            .handle => |right_handle| left_handle.value == right_handle.value,
            else => false,
        },
        .registered_name => |left_name| switch (right) {
            .registered_name => |right_name| std.mem.eql(u8, left_name, right_name),
            else => false,
        },
    };
}

fn namedIndicesEql(left: []const realization.NamedIndex, right: []const realization.NamedIndex) bool {
    if (left.len != right.len) return false;
    for (left, right) |left_index, right_index| {
        if (left_index.kind != right_index.kind) return false;
        if (!std.mem.eql(u8, left_index.name, right_index.name)) return false;
    }
    return true;
}

fn optionalStringEql(left: ?[]const u8, right: ?[]const u8) bool {
    if (left == null or right == null) return left == null and right == null;
    return std.mem.eql(u8, left.?, right.?);
}

fn cloneRequest(allocator: std.mem.Allocator, request: InvariantBasisRequest) !InvariantBasisRequest {
    const external_legs = try cloneExternalLegs(allocator, request.external_legs);
    errdefer freeExternalLegs(allocator, external_legs);

    return .{
        .algebra = request.algebra,
        .external_legs = external_legs,
        .target = request.target,
        .tree_policy = try cloneTreePolicy(allocator, request.tree_policy),
        .basis_policy = request.basis_policy,
    };
}

fn freeRequest(allocator: std.mem.Allocator, request: InvariantBasisRequest) void {
    freeExternalLegs(allocator, request.external_legs);
    switch (request.tree_policy) {
        .fixed => |fixed| allocator.free(fixed),
        .auto => {},
    }
}

fn cloneTreePolicy(allocator: std.mem.Allocator, policy: TreePolicy) !TreePolicy {
    return switch (policy) {
        .auto => .auto,
        .fixed => |fixed| .{ .fixed = try allocator.dupe(u16, fixed) },
    };
}

fn cloneExternalLegs(allocator: std.mem.Allocator, legs: []const realization.ExternalLeg) ![]realization.ExternalLeg {
    const owned = try allocator.alloc(realization.ExternalLeg, legs.len);
    var initialized: usize = 0;
    errdefer {
        for (owned[0..initialized]) |leg| freeExternalLeg(allocator, leg);
        allocator.free(owned);
    }

    for (legs, owned[0..]) |source, *target| {
        target.* = try cloneExternalLeg(allocator, source);
        initialized += 1;
    }
    return owned;
}

fn freeExternalLegs(allocator: std.mem.Allocator, legs: []const realization.ExternalLeg) void {
    for (legs) |leg| freeExternalLeg(allocator, leg);
    allocator.free(legs);
}

fn cloneExternalLeg(allocator: std.mem.Allocator, leg: realization.ExternalLeg) !realization.ExternalLeg {
    const indices = try cloneNamedIndices(allocator, leg.indices);
    errdefer freeNamedIndices(allocator, indices);

    const label = if (leg.label) |value| try allocator.dupe(u8, value) else null;
    errdefer if (label) |value| allocator.free(value);

    const ref = try cloneRealizationRef(allocator, leg.realization);
    errdefer freeRealizationRef(allocator, ref);

    return .{ .realization = ref, .indices = indices, .label = label };
}

fn freeExternalLeg(allocator: std.mem.Allocator, leg: realization.ExternalLeg) void {
    freeRealizationRef(allocator, leg.realization);
    freeNamedIndices(allocator, leg.indices);
    if (leg.label) |label| allocator.free(label);
}

fn cloneRealizationRef(allocator: std.mem.Allocator, ref: realization.RealizationRef) !realization.RealizationRef {
    return switch (ref) {
        .primitive_irrep => |irrep| .{ .primitive_irrep = irrep },
        .handle => |handle| .{ .handle = handle },
        .registered_name => |name| .{ .registered_name = try allocator.dupe(u8, name) },
    };
}

fn freeRealizationRef(allocator: std.mem.Allocator, ref: realization.RealizationRef) void {
    switch (ref) {
        .registered_name => |name| allocator.free(name),
        .primitive_irrep, .handle => {},
    }
}

fn cloneNamedIndices(allocator: std.mem.Allocator, indices: []const realization.NamedIndex) ![]realization.NamedIndex {
    const owned = try allocator.alloc(realization.NamedIndex, indices.len);
    var initialized: usize = 0;
    errdefer {
        for (owned[0..initialized]) |index| allocator.free(index.name);
        allocator.free(owned);
    }

    for (indices, owned[0..]) |source, *target| {
        target.* = .{
            .kind = source.kind,
            .name = try allocator.dupe(u8, source.name),
        };
        initialized += 1;
    }
    return owned;
}

fn freeNamedIndices(allocator: std.mem.Allocator, indices: []const realization.NamedIndex) void {
    for (indices) |index| allocator.free(index.name);
    allocator.free(indices);
}
