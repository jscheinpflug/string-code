/// tensor exposes tensor-code data structures and tensor handles.
pub const tensor = @import("tensor-code");
/// cft exposes the selected worldsheet CFT public API.
pub const cft = @import("cft-code");

test "top-level API exposes tensor and cft boundaries" {
    const testing = @import("std").testing;
    try testing.expect(@hasDecl(@This(), "tensor"));
    try testing.expect(@hasDecl(@This(), "cft"));
    try testing.expect(@hasDecl(cft, "FreeBoson"));
    try testing.expect(@hasDecl(cft, "Bc"));
    try testing.expect(@hasDecl(cft, "FreeFermion"));
    try testing.expect(@hasDecl(cft, "EtaXi"));
    try testing.expect(@hasDecl(cft, "product"));
    try testing.expect(@hasDecl(cft, "boundary"));
    try testing.expect(@hasDecl(cft.FreeBoson, "make"));
    try testing.expect(@hasDecl(cft.FreeBoson, "boundary"));
    try testing.expect(@hasDecl(cft.Bc, "sphere"));
    try testing.expect(@hasDecl(cft.Bc, "diskBoundary"));
    try testing.expect(@hasDecl(cft.FreeFermion, "sphere"));
    try testing.expect(@hasDecl(cft.EtaXi, "sphere"));
    try testing.expect(!@hasDecl(cft.FreeBoson, "Config"));
    try testing.expect(!@hasDecl(cft.FreeBoson, "BoundaryConfig"));
    try testing.expect(!@hasDecl(cft.Bc, "SphereConfig"));
    try testing.expect(!@hasDecl(cft.Bc, "DiskConfig"));
    try testing.expect(!@hasDecl(cft.FreeFermion, "SphereConfig"));
    try testing.expect(!@hasDecl(cft.EtaXi, "SphereConfig"));
    try testing.expect(!@hasDecl(cft, "Handle"));
    try testing.expect(!@hasDecl(cft, "scalars"));
    try testing.expect(!@hasDecl(cft, "freeBoson"));
    try testing.expect(!@hasDecl(cft, "bcSphere"));
    try testing.expect(!@hasDecl(cft, "freeFermionSphere"));
    try testing.expect(!@hasDecl(cft, "etaXiSphere"));
    try testing.expect(!@hasDecl(cft, "freeBosonBoundary"));
    try testing.expect(!@hasDecl(cft, "bcDiskBoundary"));
    try testing.expect(!@hasDecl(cft, "presets"));
    try testing.expect(!@hasDecl(cft, "kernel"));
    try testing.expect(!@hasDecl(cft, "theory"));
    try testing.expect(!@hasDecl(cft, "expressions"));
}

test "tensor context interns projected realization requests without expansion" {
    const testing = @import("std").testing;

    var ctx = try tensor.Context.init(testing.allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const so10_again = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    try testing.expectEqual(so10.value, so10_again.value);

    const vector = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 0 } });
    const spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 0, 0, 0, 0, 1 } });
    const vector_spinor = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 1 } });
    const vector_spinor_again = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0, 0, 0, 1 } });
    try testing.expectEqual(vector_spinor.value, vector_spinor_again.value);
    try testing.expectEqual(@as(u128, 10), ctx.irrepMetadata(vector).?.dimension.?);
    try testing.expectEqual(@as(u128, 16), ctx.irrepMetadata(spinor).?.dimension.?);
    try testing.expectEqual(@as(u128, 144), ctx.irrepMetadata(vector_spinor).?.dimension.?);
    const conjugate_spinor = try ctx.dualIrrep(spinor);
    try testing.expect(conjugate_spinor.value != spinor.value);
    try testing.expectEqual(spinor.value, (try ctx.dualIrrep(conjugate_spinor)).value);
    try testing.expectError(error.InvalidDynkinRank, ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 0 } }));

    const su2 = try ctx.registerAlgebra(.{ .simple = .{ .family = .a, .rank = 1 } });
    const fundamental = try ctx.registerIrrep(su2, .{ .dynkin = &.{1} });
    try testing.expectError(error.MixedRealizationAlgebras, ctx.registerRealization(tensor.RealizationSpec.projected(vector_spinor, &.{fundamental}, &.{
        .init(.vector, "m"),
        .init(.spinor, "a"),
    }, 0)));

    const channel = tensor.RealizationChannel.first(vector_spinor);
    const realization = try ctx.registerRealization(tensor.RealizationSpec.projectedChannel(channel, &.{ vector, spinor }, &.{
        .init(.vector, "m"),
        .init(.spinor, "a"),
    }).named("SO10.vector_spinor"));
    const realization_again = try ctx.registerRealization(tensor.RealizationSpec.projectedChannel(channel, &.{ vector, spinor }, &.{
        .init(.vector, "m"),
        .init(.spinor, "a"),
    }).named("SO10.vector_spinor"));
    try testing.expectEqual(realization.value, realization_again.value);

    const leg = tensor.ExternalLeg.realized(realization, &.{
        .init(.vector, "m1"),
        .init(.spinor, "a1"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ leg, leg, leg, leg, leg, leg },
    });
    const basis_again = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ leg, leg, leg, leg, leg, leg },
    });
    try testing.expectEqual(basis.value, basis_again.value);

    try testing.expectError(error.MixedInvariantAlgebras, ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{tensor.ExternalLeg.primitive(fundamental, &.{
            .init(.fundamental, "i"),
        })},
    }));

    const so9 = try ctx.registerAlgebra(.{ .simple = .{ .family = .b, .rank = 4 } });
    const so9_vector = try ctx.registerIrrep(so9, .{ .dynkin = &.{ 1, 0, 0, 0 } });
    const so9_spinor = try ctx.registerIrrep(so9, .{ .dynkin = &.{ 0, 0, 0, 1 } });
    try testing.expectEqual(@as(u128, 9), ctx.irrepMetadata(so9_vector).?.dimension.?);
    try testing.expectEqual(@as(u128, 16), ctx.irrepMetadata(so9_spinor).?.dimension.?);

    const e6 = try ctx.registerAlgebra(.{ .simple = .{ .family = .e6, .rank = 6 } });
    const e7 = try ctx.registerAlgebra(.{ .simple = .{ .family = .e7, .rank = 7 } });
    const e8 = try ctx.registerAlgebra(.{ .simple = .{ .family = .e8, .rank = 8 } });
    const e6_27 = try ctx.registerIrrep(e6, .{ .dynkin = &.{ 1, 0, 0, 0, 0, 0 } });
    const e7_56 = try ctx.registerIrrep(e7, .{ .dynkin = &.{ 0, 0, 0, 0, 0, 1, 0 } });
    const e8_248 = try ctx.registerIrrep(e8, .{ .dynkin = &.{ 0, 0, 0, 0, 0, 0, 1, 0 } });
    try testing.expectEqual(@as(u128, 27), ctx.irrepMetadata(e6_27).?.dimension.?);
    try testing.expectEqual(@as(u128, 56), ctx.irrepMetadata(e7_56).?.dimension.?);
    try testing.expectEqual(@as(u128, 248), ctx.irrepMetadata(e8_248).?.dimension.?);
}
