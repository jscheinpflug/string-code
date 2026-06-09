const preset_impl = @import("presets.zig");

/// FreeBoson groups the public free-boson preset constructors.
pub const FreeBoson = preset_impl.FreeBoson;
/// Bc groups the public bc-ghost preset constructors.
pub const Bc = preset_impl.Bc;
/// FreeFermion groups the public NS free-fermion preset constructors.
pub const FreeFermion = preset_impl.FreeFermion;
/// IndexSort classifies typed target indices accepted by runtime preset builders.
pub const IndexSort = @import("presets/shared.zig").IndexSort;
/// PrimitivePairKernels exposes primitive free-field pair-kernel classifiers.
pub const PrimitivePairKernels = @import("presets/primitive_pair_kernels.zig");
/// EtaXi groups the public eta-xi preset constructors.
pub const EtaXi = preset_impl.EtaXi;
/// product builds the generated preset type for a product of independent bulk presets.
pub const product = preset_impl.product;
/// boundary builds the generated preset type for a BCFT from a bulk preset and boundary extensions.
pub const boundary = preset_impl.boundary;

test "root CFT API exposes selected constructors without implementation namespaces" {
    const testing = @import("std").testing;
    try testing.expect(@hasDecl(@This(), "FreeBoson"));
    try testing.expect(@hasDecl(@This(), "Bc"));
    try testing.expect(@hasDecl(@This(), "FreeFermion"));
    try testing.expect(@hasDecl(@This(), "IndexSort"));
    try testing.expect(@hasDecl(@This(), "PrimitivePairKernels"));
    try testing.expect(@hasDecl(@This(), "EtaXi"));
    try testing.expect(@hasDecl(@This(), "product"));
    try testing.expect(@hasDecl(@This(), "boundary"));
    try testing.expect(@hasDecl(FreeBoson, "make"));
    try testing.expect(@hasDecl(FreeBoson, "boundary"));
    try testing.expect(@hasDecl(Bc, "sphere"));
    try testing.expect(@hasDecl(Bc, "diskBoundary"));
    try testing.expect(@hasDecl(FreeFermion, "sphere"));
    try testing.expect(@hasDecl(EtaXi, "sphere"));
    try testing.expect(!@hasDecl(FreeBoson, "Config"));
    try testing.expect(!@hasDecl(FreeBoson, "BoundaryConfig"));
    try testing.expect(!@hasDecl(Bc, "SphereConfig"));
    try testing.expect(!@hasDecl(Bc, "DiskConfig"));
    try testing.expect(!@hasDecl(FreeFermion, "SphereConfig"));
    try testing.expect(!@hasDecl(EtaXi, "SphereConfig"));
    try testing.expect(!@hasDecl(@This(), "Handle"));
    try testing.expect(!@hasDecl(@This(), "scalars"));
    try testing.expect(!@hasDecl(@This(), "freeBoson"));
    try testing.expect(!@hasDecl(@This(), "bcSphere"));
    try testing.expect(!@hasDecl(@This(), "freeFermionSphere"));
    try testing.expect(!@hasDecl(@This(), "etaXiSphere"));
    try testing.expect(!@hasDecl(@This(), "freeBosonBoundary"));
    try testing.expect(!@hasDecl(@This(), "bcDiskBoundary"));
    try testing.expect(!@hasDecl(@This(), "presets"));
    try testing.expect(!@hasDecl(@This(), "kernel"));
    try testing.expect(!@hasDecl(@This(), "theory"));
    try testing.expect(!@hasDecl(@This(), "expressions"));
    try testing.expect(!@hasDecl(@This(), "Generated"));
}
