const kernel = @import("../kernel.zig");

/// Group is the compact id stored on local operators in one normal product.
pub const Group = u16;

/// none marks an operator that is not inside a normal-ordered product.
pub const none: Group = 0;

/// first is the first valid context-local normal-ordering group id.
pub const first: Group = 1;

/// next returns a fresh normal-ordering group and advances the counter.
pub fn next(counter: *Group) !Group {
    if (counter.* == none) return error.TooManyNormalOrderedProducts;
    const group = counter.*;
    counter.* +%= 1;
    return group;
}

/// tag returns OP marked as part of GROUP.
pub fn tag(op: kernel.Call.LocalOp, group: Group) kernel.Call.LocalOp {
    var tagged = op;
    tagged.normal_order_group = group;
    return tagged;
}

/// same reports whether two operators are in the same nonempty normal product.
pub fn same(left: kernel.Call.LocalOp, right: kernel.Call.LocalOp) bool {
    const group = left.normal_order_group;
    return group != none and group == right.normal_order_group;
}

/// tagLast marks the last COUNT operators as one normal-ordered product.
pub fn tagLast(ops: []kernel.Call.LocalOp, count: usize, counter: *Group) !void {
    if (count == 0 or count > ops.len) return error.InvalidNormalOrderGroup;
    const group = try next(counter);
    const start = ops.len - count;
    for (ops[start..]) |*op| {
        op.* = tag(op.*, group);
    }
}
