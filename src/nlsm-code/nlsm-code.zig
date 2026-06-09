const geometry = @import("local_geometry_reducer.zig");

/// GeometryFlavor selects the target-geometry quotient used by local reducers.
pub const GeometryFlavor = geometry.GeometryFlavor;
/// TensorSlotSort classifies a target tensor slot by complex type and variance.
pub const TensorSlotSort = geometry.TensorSlotSort;
/// TensorSlot is one compact target-index occurrence in a local tensor atom.
pub const TensorSlot = geometry.TensorSlot;
/// TensorAtom is one local geometry tensor row.
pub const TensorAtom = geometry.TensorAtom;
/// TensorTerm is a streamed product of local geometry atoms.
pub const TensorTerm = geometry.TensorTerm;
/// ReductionOptions selects the local quotient checks applied to one term.
pub const ReductionOptions = geometry.ReductionOptions;
/// ReductionSummary reports the reducer decision without materializing a sum.
pub const ReductionSummary = geometry.ReductionSummary;
/// reduceLocalTerm filters one streamed local geometry term into caller storage.
pub const reduceLocalTerm = geometry.reduceLocalTerm;

test "nlsm root exposes only compact local reducer rows" {
    const testing = @import("std").testing;
    try testing.expect(@hasDecl(@This(), "GeometryFlavor"));
    try testing.expect(@hasDecl(@This(), "TensorSlotSort"));
    try testing.expect(@hasDecl(@This(), "reduceLocalTerm"));
    try testing.expect(!@hasDecl(@This(), "local_geometry_reducer"));
}
