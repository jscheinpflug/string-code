const presets = @import("presets.zig");

/// Handle groups compact ids used by generated preset operator builders.
pub const Handle = presets.Handle;
/// scalars exposes scalar atoms and exact scalar helpers used in convention choices.
pub const scalars = presets.scalars;

/// FreeBoson groups the public free-boson preset constructors and configs.
pub const FreeBoson = presets.FreeBoson;
/// Bc groups the public bc-ghost preset constructors and configs.
pub const Bc = presets.Bc;
/// product builds the generated preset type for a product of independent bulk presets.
pub const product = presets.product;
/// boundary builds the generated preset type for a BCFT from a bulk preset and boundary extensions.
pub const boundary = presets.boundary;

test "root CFT API exposes selected constructors without implementation namespaces" {
    const testing = @import("std").testing;
    try testing.expect(@hasDecl(@This(), "FreeBoson"));
    try testing.expect(@hasDecl(@This(), "Bc"));
    try testing.expect(@hasDecl(@This(), "product"));
    try testing.expect(@hasDecl(@This(), "boundary"));
    try testing.expect(@hasDecl(FreeBoson, "make"));
    try testing.expect(@hasDecl(FreeBoson, "boundary"));
    try testing.expect(@hasDecl(Bc, "sphere"));
    try testing.expect(@hasDecl(Bc, "diskBoundary"));
    try testing.expect(!@hasDecl(@This(), "freeBoson"));
    try testing.expect(!@hasDecl(@This(), "bcSphere"));
    try testing.expect(!@hasDecl(@This(), "freeBosonBoundary"));
    try testing.expect(!@hasDecl(@This(), "bcDiskBoundary"));
    try testing.expect(!@hasDecl(@This(), "presets"));
    try testing.expect(!@hasDecl(@This(), "kernel"));
    try testing.expect(!@hasDecl(@This(), "theory"));
    try testing.expect(!@hasDecl(@This(), "expressions"));
}
