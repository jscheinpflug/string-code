const shared = @import("presets/shared.zig");
const free_boson = @import("presets/free_boson.zig");
const bc = @import("presets/bc.zig");
const composition = @import("presets/composition.zig");

const freeBoson = free_boson.freeBoson;
const bcSphere = bc.bcSphere;
const freeBosonBoundary = free_boson.boundaryExtension;
const bcDiskBoundary = bc.boundaryExtension;

/// Handle groups compact ids used by preset operator builders.
pub const Handle = shared.Handle;
/// scalars exposes basic algebra for compact structured rule scalars.
pub const scalars = shared.scalars;

/// FreeBoson groups the free-boson preset constructors and configs.
pub const FreeBoson = struct {
    /// Config declares a noncompact D-dimensional free-boson preset.
    pub const Config = free_boson.FreeBosonConfig;
    /// BoundaryConfig declares Neumann and Dirichlet data for a brane.
    pub const BoundaryConfig = free_boson.FreeBosonBoundaryConfig;

    /// make builds the generated preset type for a noncompact free-boson CFT.
    pub const make = free_boson.freeBoson;
    /// boundary declares the Neumann/Dirichlet free-boson boundary extension.
    pub const boundary = free_boson.boundaryExtension;
};

/// Bc groups the bc-ghost preset constructors and configs.
pub const Bc = struct {
    /// SphereConfig declares the holomorphic bc system and optional antiholomorphic copy.
    pub const SphereConfig = bc.BcSphereConfig;
    /// DiskConfig declares the disk boundary extension for the bc ghost system.
    pub const DiskConfig = bc.BcDiskConfig;

    /// sphere builds the generated preset type for the sphere bc ghost CFT.
    pub const sphere = bc.bcSphere;
    /// diskBoundary declares boundary and mixed bulk-boundary bc rules on the disk.
    pub const diskBoundary = bc.boundaryExtension;
};

/// product builds the generated preset type for a product of independent bulk presets.
pub const product = composition.product;
/// boundary builds the generated preset type for a BCFT from a bulk preset and boundary extensions.
pub const boundary = composition.boundary;

test "presets compose operator builders without exposing theory tables" {
    const testing = @import("std").testing;

    const X = freeBoson(.{ .dimension = 26 });
    const BosonicSphere = product(.{ X, bcSphere(.{}) });
    const BosonicDisk = boundary(BosonicSphere, .{
        freeBosonBoundary(.{
            .neumann = X.target.subspace(&.{ 0, 1, 2, 3 }),
            .dirichlet = X.target.complement(&.{ 0, 1, 2, 3 }),
            .dirichlet_position = X.target.point("x0"),
            .chan_paton = X.target.boundaryStack("stack"),
        }),
        bcDiskBoundary(.{}),
    });

    var local = BosonicDisk.local(testing.allocator);
    defer local.deinit();

    const k = try local.momentum("k");
    const y = try local.boundaryCoord("y");
    const x = try BosonicDisk.op.free_boson_boundary.expXBoundary(&local, k, y);
    const c = try BosonicDisk.op.bc_boundary.cBoundary(&local, 0, y);
    const ops = try local.ops(.{ x, c });

    try testing.expectEqual(@as(usize, 16), BosonicDisk.config.disk.wick_rules.len);
    try testing.expectEqual(@as(usize, 30), BosonicDisk.config.disk.wick_rule_index.len);
    try testing.expectEqual(@as(usize, 2), BosonicDisk.config.disk.zero_modes.len);
    try testing.expectEqual(@as(usize, 6), BosonicDisk.config.disk.config_entries.len);
    switch (BosonicDisk.config.disk.config_entries[0].value) {
        .target_dimension => |dimension| try testing.expectEqual(@as(u16, 26), dimension),
        else => return error.UnexpectedBulkConfig,
    }
    switch (BosonicDisk.config.disk.config_entries[1].value) {
        .tensor_projector => |projector| try testing.expectEqual(@intFromEnum(X.target.subspace(&.{ 0, 1, 2, 3 })), @intFromEnum(projector)),
        else => return error.UnexpectedBoundaryConfig,
    }
    switch (BosonicDisk.config.disk.config_entries[5].value) {
        .boundary_stack => |stack| try testing.expectEqual(@intFromEnum(X.target.boundaryStack("stack")), @intFromEnum(stack)),
        else => return error.UnexpectedBoundaryStack,
    }
    try testing.expectEqual(@as(usize, 1), X.config.sphere.config_entries.len);
    switch (X.config.sphere.config_entries[0].value) {
        .target_dimension => |dimension| try testing.expectEqual(@as(u16, 26), dimension),
        else => return error.UnexpectedBulkConfig,
    }
    try testing.expectEqual(@as(usize, 2), ops.operators.len);
    switch (ops.labels.values[@intCast(ops.operators[0].labels)]) {
        .symbol => |value| try testing.expectEqual(@intFromEnum(k), value),
        else => return error.UnexpectedLabelKind,
    }
}

test "preset rules and namespaces compose from supplied factors" {
    const testing = @import("std").testing;

    const X = freeBoson(.{ .dimension = 10 });
    const Ghost = bcSphere(.{});
    const MatterOnly = product(.{X});
    const GhostOnly = product(.{Ghost});
    const MatterGhost = product(.{ X, Ghost });

    try testing.expect(@hasDecl(MatterOnly.op, "free_boson"));
    try testing.expect(!@hasDecl(MatterOnly.op, "bc"));
    try testing.expect(@hasDecl(GhostOnly.op, "bc"));
    try testing.expect(!@hasDecl(GhostOnly.op, "free_boson"));
    try testing.expectEqual(@as(usize, 7), MatterOnly.config.sphere.wick_rules.len);
    try testing.expectEqual(@as(usize, 2), GhostOnly.config.sphere.wick_rules.len);
    try testing.expectEqual(@as(usize, 9), MatterGhost.config.sphere.wick_rules.len);
    try testing.expectEqual(@as(usize, 15), MatterGhost.config.sphere.wick_rule_index.len);

    const DiskMatter = boundary(MatterGhost, .{
        freeBosonBoundary(.{
            .neumann = X.target.subspace(&.{ 0, 1, 2, 3 }),
            .dirichlet = X.target.complement(&.{ 0, 1, 2, 3 }),
            .dirichlet_position = X.target.point("x0"),
        }),
    });
    const DiskMatterGhost = boundary(MatterGhost, .{
        freeBosonBoundary(.{
            .neumann = X.target.subspace(&.{ 0, 1, 2, 3 }),
            .dirichlet = X.target.complement(&.{ 0, 1, 2, 3 }),
            .dirichlet_position = X.target.point("x0"),
        }),
        bcDiskBoundary(.{}),
    });

    try testing.expect(@hasDecl(DiskMatter.op, "bulk"));
    try testing.expect(@hasDecl(DiskMatter.op, "free_boson_boundary"));
    try testing.expect(!@hasDecl(DiskMatter.op, "bc_boundary"));
    try testing.expect(@hasDecl(DiskMatterGhost.op, "bc_boundary"));
    try testing.expectEqual(@as(usize, 11), DiskMatter.config.disk.wick_rules.len);
    try testing.expectEqual(@as(usize, 16), DiskMatterGhost.config.disk.wick_rules.len);
}

test "preset compile-time flags change generated rule surfaces" {
    const testing = @import("std").testing;

    const X = freeBoson(.{ .dimension = 10 });
    const HolomorphicBc = bcSphere(.{ .include_antiholomorphic_copy = false });
    const MatterGhost = product(.{ X, HolomorphicBc });
    const BoundaryOnlyGhost = boundary(HolomorphicBc, .{
        bcDiskBoundary(.{ .include_mixed_bulk_boundary = false }),
    });

    try testing.expect(@hasDecl(HolomorphicBc.op, "b"));
    try testing.expect(!@hasDecl(HolomorphicBc.op, "bt"));
    try testing.expectEqual(@as(usize, 1), HolomorphicBc.config.sphere.wick_rules.len);
    try testing.expectEqual(@as(usize, 8), MatterGhost.config.sphere.wick_rules.len);
    try testing.expectEqual(@as(usize, 1), BoundaryOnlyGhost.config.disk.wick_rules.len);
}

test "bc zero modes consume c jets by top-form saturation" {
    const testing = @import("std").testing;

    const Ghost = bcSphere(.{ .include_antiholomorphic_copy = false });

    var local = Ghost.local(testing.allocator);
    defer local.deinit();

    const z1 = try local.coord("z1");
    const z2 = try local.coord("z2");
    const z3 = try local.coord("z3");
    const ops = try local.ops(.{
        try Ghost.op.c(&local, 0, z1),
        try Ghost.op.c(&local, 1, z2),
        try Ghost.op.c(&local, 2, z3),
    });

    const Sink = struct {
        factor_count: usize = 0,
        base_end_count: usize = 0,
        derivative_sum: u16 = 0,

        /// emitZeroModeFactor records the top-form factor emitted by the base case.
        pub fn emitZeroModeFactor(self: *@This(), factor: anytype) !void {
            self.factor_count += 1;
            switch (factor) {
                .bc_top_form => |top| {
                    if (top.support != .sphere_holomorphic) return error.UnexpectedBcSupport;
                    self.derivative_sum = @as(u16, top.jets[0].derivative_order) + top.jets[1].derivative_order + top.jets[2].derivative_order;
                },
                else => return error.UnexpectedZeroModeFactor,
            }
        }

        /// emitZeroModeBaseEnd records that every residual insertion was consumed.
        pub fn emitZeroModeBaseEnd(self: *@This()) !void {
            self.base_end_count += 1;
        }
    };

    var sink = Sink{};
    try testing.expect(try shared.emitZeroModeBaseCase(&Ghost.config.sphere, ops, null, &sink));
    try testing.expectEqual(@as(usize, 1), sink.factor_count);
    try testing.expectEqual(@as(usize, 1), sink.base_end_count);
    try testing.expectEqual(@as(u16, 3), sink.derivative_sum);
}

test "disk bc zero modes use one doubled chiral top form" {
    const testing = @import("std").testing;

    const Ghost = bcSphere(.{});
    const Disk = boundary(Ghost, .{bcDiskBoundary(.{})});

    var local = Disk.local(testing.allocator);
    defer local.deinit();

    const z = try local.coord("z");
    const zbar = try local.coord("zbar");
    const y = try local.boundaryCoord("y");
    const ops = try local.ops(.{
        try Disk.op.bulk.c(&local, 0, z),
        try Disk.op.bulk.ct(&local, 0, zbar),
        try Disk.op.bc_boundary.cBoundary(&local, 0, y),
    });

    const Sink = struct {
        saw_disk_doubled: bool = false,

        /// emitZeroModeFactor records whether the doubled disk top form was emitted.
        pub fn emitZeroModeFactor(self: *@This(), factor: anytype) !void {
            switch (factor) {
                .bc_top_form => |top| self.saw_disk_doubled = top.support == .disk_doubled,
                else => return error.UnexpectedZeroModeFactor,
            }
        }

        /// emitZeroModeBaseEnd accepts the successful zero-mode base case.
        pub fn emitZeroModeBaseEnd(self: *@This()) !void {
            _ = self;
        }
    };

    var sink = Sink{};
    try testing.expect(try shared.emitZeroModeBaseCase(&Disk.config.disk, ops, null, &sink));
    try testing.expect(sink.saw_disk_doubled);
}

test "free boson zero modes emit momentum delta and profile presentations" {
    const testing = @import("std").testing;

    const X = freeBoson(.{ .dimension = 10 });

    var local = X.local(testing.allocator);
    defer local.deinit();

    const k = try local.momentum("k");
    const z = try local.coord("z");
    const zbar = try local.coord("zbar");
    const f0 = try local.targetFunction("f");
    const fhat = try local.fourierTransform("fhat");
    const coeff = try local.profileCoefficient("a");
    const point = try local.targetPoint("x0");
    const position_profile = X.profile.positionSpace(f0);
    const fourier_profile = X.profile.fourier(fhat);
    const polynomial_profile = X.profile.polynomialRnc(point, &.{.{ .coefficient = coeff, .power = 2 }});
    const ops = try local.ops(.{
        try X.op.expX(&local, k, z, zbar),
        try X.op.profile(&local, position_profile, z, zbar),
        try X.op.profile(&local, fourier_profile, z, zbar),
        try X.op.profile(&local, polynomial_profile, z, zbar),
    });

    const Sink = struct {
        delta_count: usize = 0,
        gaussian_count: usize = 0,
        fourier_count: usize = 0,
        polynomial_count: usize = 0,
        base_end_count: usize = 0,
        two_pi_power: u16 = 0,

        /// emitZeroModeFactor records each free-boson zero-mode factor by presentation.
        pub fn emitZeroModeFactor(self: *@This(), factor: anytype) !void {
            switch (factor) {
                .momentum_delta => |delta| {
                    self.delta_count += 1;
                    self.two_pi_power = delta.two_pi_power;
                    if (delta.projector != null or delta.momenta.len != 1) return error.UnexpectedMomentumDelta;
                },
                .profile_gaussian_differential => self.gaussian_count += 1,
                .profile_fourier_integral => self.fourier_count += 1,
                .profile_polynomial_integral => self.polynomial_count += 1,
                else => return error.UnexpectedZeroModeFactor,
            }
        }

        /// emitZeroModeBaseEnd records that all profile and plane-wave residuals were consumed.
        pub fn emitZeroModeBaseEnd(self: *@This()) !void {
            self.base_end_count += 1;
        }
    };

    var sink = Sink{};
    try testing.expect(try shared.emitZeroModeBaseCase(&X.config.sphere, ops, null, &sink));
    try testing.expectEqual(@as(usize, 1), sink.delta_count);
    try testing.expectEqual(@as(u16, 10), sink.two_pi_power);
    try testing.expectEqual(@as(usize, 1), sink.gaussian_count);
    try testing.expectEqual(@as(usize, 1), sink.fourier_count);
    try testing.expectEqual(@as(usize, 1), sink.polynomial_count);
    try testing.expectEqual(@as(usize, 1), sink.base_end_count);
}

test "disk free boson zero modes emit Neumann delta and Dirichlet phase" {
    const testing = @import("std").testing;

    const X = freeBoson(.{ .dimension = 10 });
    const Disk = boundary(product(.{X}), .{
        freeBosonBoundary(.{
            .neumann = X.target.subspace(&.{ 0, 1, 2, 3 }),
            .dirichlet = X.target.complement(&.{ 0, 1, 2, 3 }),
            .dirichlet_position = X.target.point("x0"),
        }),
    });

    var local = Disk.local(testing.allocator);
    defer local.deinit();

    const k = try local.momentum("k");
    const y = try local.boundaryCoord("y");
    const ops = try local.ops(.{
        try Disk.op.free_boson_boundary.expXBoundary(&local, k, y),
    });

    const Sink = struct {
        delta_count: usize = 0,
        phase_count: usize = 0,
        base_end_count: usize = 0,
        two_pi_power: u16 = 0,
        saw_disk_scalar: bool = false,
        saw_projector: bool = false,
        saw_position: bool = false,

        /// emitZeroModeFactor records Neumann momentum conservation and Dirichlet phase data.
        pub fn emitZeroModeFactor(self: *@This(), factor: anytype) !void {
            switch (factor) {
                .momentum_delta => |delta| {
                    self.delta_count += 1;
                    self.two_pi_power = delta.two_pi_power;
                    self.saw_projector = delta.projector != null;
                    switch (delta.scalar) {
                        .monomial => |monomial| self.saw_disk_scalar = monomial.atom != null and monomial.atom_power == 1,
                        else => return error.UnexpectedDiskNormalization,
                    }
                    if (delta.momenta.len != 1) return error.UnexpectedMomentumDelta;
                },
                .dirichlet_phase => |phase| {
                    self.phase_count += 1;
                    self.saw_position = phase.momenta.len == 1;
                    switch (phase.position) {
                        .target_point => {},
                        else => return error.UnexpectedDirichletPosition,
                    }
                },
                else => return error.UnexpectedZeroModeFactor,
            }
        }

        /// emitZeroModeBaseEnd records that the disk constant mode consumed the insertion.
        pub fn emitZeroModeBaseEnd(self: *@This()) !void {
            self.base_end_count += 1;
        }
    };

    var sink = Sink{};
    try testing.expect(try shared.emitZeroModeBaseCase(&Disk.config.disk, ops, null, &sink));
    try testing.expectEqual(@as(usize, 1), sink.delta_count);
    try testing.expectEqual(@as(usize, 1), sink.phase_count);
    try testing.expectEqual(@as(u16, 4), sink.two_pi_power);
    try testing.expect(sink.saw_disk_scalar);
    try testing.expect(sink.saw_projector);
    try testing.expect(sink.saw_position);
    try testing.expectEqual(@as(usize, 1), sink.base_end_count);
}

test "unconsumed free boson derivative kills the zero-mode base case" {
    const testing = @import("std").testing;

    const X = freeBoson(.{ .dimension = 10 });

    var local = X.local(testing.allocator);
    defer local.deinit();

    const mu = try local.index("mu");
    const z = try local.coord("z");
    const ops = try local.ops(.{
        try X.op.dX(&local, mu, 0, z),
    });

    const Sink = struct {
        /// emitZeroModeFactor fails if an unconsumed derivative field emits a zero-mode factor.
        pub fn emitZeroModeFactor(_: *@This(), _: anytype) !void {
            return error.UnexpectedZeroModeFactor;
        }

        /// emitZeroModeBaseEnd fails because the derivative residual should not be consumed.
        pub fn emitZeroModeBaseEnd(_: *@This()) !void {
            return error.UnexpectedZeroModeBaseEnd;
        }
    };

    var sink = Sink{};
    try testing.expect(!try shared.emitZeroModeBaseCase(&X.config.sphere, ops, null, &sink));
}

test "presets expose physics-named Wick rule templates" {
    const testing = @import("std").testing;

    const X = freeBoson(.{ .dimension = 10, .alpha_prime = scalars.atom("test_free_boson", "custom_alpha_prime") });
    const custom_alpha = scalars.atom("test_free_boson", "custom_alpha_prime");
    const Ghost = bcSphere(.{});
    const Disk = boundary(product(.{ X, Ghost }), .{
        freeBosonBoundary(.{
            .neumann = X.target.subspace(&.{ 0, 1, 2, 3 }),
            .dirichlet = X.target.complement(&.{ 0, 1, 2, 3 }),
            .dirichlet_position = X.target.point("x0"),
        }),
        bcDiskBoundary(.{}),
    });

    switch (scalars.rational(2, 4)) {
        .rational => |value| {
            try testing.expectEqual(@as(i64, 1), value.numerator);
            try testing.expectEqual(@as(i64, 2), value.denominator);
        },
        else => return error.UnexpectedScalarShape,
    }

    try testing.expectEqual(@as(usize, 7), X.rules.sphere_wick.len);
    try testing.expectEqual(@as(usize, 1), X.rules.sphere_wick[0].expr.terms.len);
    switch (X.rules.sphere_wick[0].expr.terms[0].coordinates[0]) {
        .difference_power => |factor| {
            try testing.expectEqual(@as(i16, -2), factor.exponent);
            try testing.expectEqual(.left, factor.coordinate.left.side);
            try testing.expect(factor.derivatives.include_left);
            try testing.expect(factor.derivatives.include_right);
        },
        else => return error.UnexpectedCoordinateFactor,
    }
    switch (X.rules.sphere_wick[0].expr.terms[0].scalars[0]) {
        .value => |scalar| switch (scalar) {
            .monomial => |monomial| {
                try testing.expectEqual(@as(i64, 1), monomial.rational.numerator);
                try testing.expectEqual(@as(i64, 2), monomial.rational.denominator);
                try testing.expectEqual(@as(u2, 0), monomial.imaginary_power);
                try testing.expectEqual(@as(i8, 1), monomial.atom_power);
                try testing.expectEqual(custom_alpha, monomial.atom.?);
            },
            else => return error.UnexpectedScalarShape,
        },
        else => return error.UnexpectedScalarFactor,
    }
    switch (Ghost.rules.sphere_wick[0].expr.terms[0].coordinates[0]) {
        .difference_power => |factor| {
            try testing.expectEqual(@as(i16, -1), factor.exponent);
            try testing.expect(factor.derivatives.include_left);
            try testing.expect(factor.derivatives.include_right);
        },
        else => return error.UnexpectedCoordinateFactor,
    }
    try testing.expectEqual(@as(usize, 2), Ghost.rules.sphere_wick.len);
    try testing.expectEqual(@as(usize, 16), Disk.rules.disk_wick.len);
}

test "pair Wick resolves derivative action on a vector profile" {
    const testing = @import("std").testing;

    const X = freeBoson(.{ .dimension = 10 });

    var local = X.local(testing.allocator);
    defer local.deinit();

    const mu = try local.index("mu");
    const nu = try local.index("nu");
    const z = try local.coord("z");
    const w = try local.coord("w");
    const wbar = try local.coord("wbar");
    const f0 = try local.targetFunction("f");
    const f = X.profile.positionSpace(f0);

    const dx = try X.op.dX(&local, mu, 0, z);
    const profile = try X.op.profileVector(&local, f, nu, w, wbar);
    const ops = try local.ops(.{ dx, profile });

    const Sink = struct {
        term_count: usize = 0,
        scalar_count: usize = 0,
        coordinate_count: usize = 0,
        tensor_count: usize = 0,
        action_count: usize = 0,
        saw_scalar: bool = false,
        saw_coordinate: bool = false,
        saw_tensor_none: bool = false,
        saw_action: bool = false,
        expected_z: u32,
        expected_w: u32,
        expected_profile: u32,
        expected_index: u32,

        /// emitWickTermStart records the single primitive profile Wick term.
        pub fn emitWickTermStart(self: *@This(), event: anytype) !void {
            if (event.left_index != 0 or event.right_index != 1 or event.term_index != 0) return error.UnexpectedWickTermEvent;
            self.term_count += 1;
        }

        /// emitWickScalar checks the expected free-boson profile scalar.
        pub fn emitWickScalar(self: *@This(), factor: anytype) !void {
            self.scalar_count += 1;
            switch (factor) {
                .value => |scalar| switch (scalar) {
                    .monomial => |monomial| {
                        if (monomial.rational.numerator != -1 or monomial.rational.denominator != 2 or monomial.atom == null) return error.UnexpectedScalarFactor;
                        self.saw_scalar = true;
                    },
                    else => return error.UnexpectedScalarFactor,
                },
                else => return error.UnexpectedScalarFactor,
            }
        }

        /// emitWickCoordinate checks the resolved profile pole.
        pub fn emitWickCoordinate(self: *@This(), factor: anytype) !void {
            self.coordinate_count += 1;
            if (factor.scalar.numerator != 1 or factor.scalar.denominator != 1) return error.UnexpectedCoordinateScalar;
            switch (factor.kernel) {
                .difference_power => |power| {
                    if (power.coordinate.left != self.expected_z or power.coordinate.right != self.expected_w or power.exponent != -1) return error.UnexpectedCoordinateFactor;
                    self.saw_coordinate = true;
                },
                else => return error.UnexpectedCoordinateFactor,
            }
        }

        /// emitWickTensor checks that no tensor numerator is emitted.
        pub fn emitWickTensor(self: *@This(), factor: anytype) !void {
            self.tensor_count += 1;
            switch (factor) {
                .none => self.saw_tensor_none = true,
                else => return error.UnexpectedTensorFactor,
            }
        }

        /// emitWickAction checks the profile-derivative action.
        pub fn emitWickAction(self: *@This(), factor: anytype) !void {
            self.action_count += 1;
            switch (factor) {
                .profile_derivative => |action| {
                    switch (action.profile) {
                        .symbol => |value| if (value != self.expected_profile) return error.UnexpectedProfileLabel,
                        else => return error.UnexpectedProfileLabel,
                    }
                    switch (action.index) {
                        .symbol => |value| if (value != self.expected_index) return error.UnexpectedIndexLabel,
                        else => return error.UnexpectedIndexLabel,
                    }
                    self.saw_action = true;
                },
                else => return error.UnexpectedProfileAction,
            }
        }

        /// emitWickTermEnd accepts the completed primitive term.
        pub fn emitWickTermEnd(self: *@This()) !void {
            _ = self;
        }
    };

    var sink = Sink{
        .expected_z = @intFromEnum(z),
        .expected_w = @intFromEnum(w),
        .expected_profile = @intFromEnum(f),
        .expected_index = @intFromEnum(mu),
    };
    try testing.expectEqual(@as(usize, 1), try shared.emitWickPairTerms(&X.config.sphere, ops, 0, 1, &sink));
    try testing.expectEqual(@as(usize, 1), sink.term_count);
    try testing.expectEqual(@as(usize, 1), sink.scalar_count);
    try testing.expectEqual(@as(usize, 1), sink.coordinate_count);
    try testing.expectEqual(@as(usize, 1), sink.tensor_count);
    try testing.expectEqual(@as(usize, 1), sink.action_count);
    try testing.expect(sink.saw_scalar);
    try testing.expect(sink.saw_coordinate);
    try testing.expect(sink.saw_tensor_none);
    try testing.expect(sink.saw_action);

    const coeff = try local.profileCoefficient("a");
    const x0 = try local.targetPoint("x0");
    const polynomial_linear = X.profile.polynomialRnc(x0, &.{.{ .coefficient = coeff, .power = 1 }});
    const polynomial_quadratic = X.profile.polynomialRnc(x0, &.{.{ .coefficient = coeff, .power = 2 }});
    try testing.expect(@intFromEnum(polynomial_linear) != @intFromEnum(polynomial_quadratic));
}

test "pair Wick resolves config-backed boundary projectors" {
    const testing = @import("std").testing;

    const X = freeBoson(.{ .dimension = 10 });
    const Disk = boundary(product(.{X}), .{
        freeBosonBoundary(.{
            .neumann = X.target.subspace(&.{ 0, 1, 2, 3 }),
            .dirichlet = X.target.complement(&.{ 0, 1, 2, 3 }),
            .dirichlet_position = X.target.point("x0"),
        }),
    });
    const neumann = X.target.subspace(&.{ 0, 1, 2, 3 });

    var local = Disk.local(testing.allocator);
    defer local.deinit();

    const mu = try local.index("mu");
    const nu = try local.index("nu");
    const y = try local.boundaryCoord("y");
    const y2 = try local.boundaryCoord("y2");
    const left = try Disk.op.free_boson_boundary.dXBoundary(&local, mu, 0, y);
    const right = try Disk.op.free_boson_boundary.dXBoundary(&local, nu, 1, y2);
    const ops = try local.ops(.{ left, right });

    const Sink = struct {
        term_count: usize = 0,
        scalar_count: usize = 0,
        coordinate_count: usize = 0,
        tensor_count: usize = 0,
        action_count: usize = 0,
        saw_scalar: bool = false,
        saw_coordinate: bool = false,
        saw_projector: bool = false,
        expected_y: u32,
        expected_y2: u32,
        expected_neumann: u32,

        /// emitWickTermStart records the single boundary Wick term.
        pub fn emitWickTermStart(self: *@This(), event: anytype) !void {
            if (event.left_index != 0 or event.right_index != 1 or event.term_index != 0) return error.UnexpectedWickTermEvent;
            self.term_count += 1;
        }

        /// emitWickScalar checks the boundary free-boson scalar factor.
        pub fn emitWickScalar(self: *@This(), factor: anytype) !void {
            self.scalar_count += 1;
            switch (factor) {
                .value => |scalar| switch (scalar) {
                    .monomial => |monomial| {
                        if (monomial.rational.numerator != 1 or monomial.rational.denominator != 1 or monomial.atom == null) return error.UnexpectedScalarFactor;
                        self.saw_scalar = true;
                    },
                    else => return error.UnexpectedScalarFactor,
                },
                else => return error.UnexpectedScalarFactor,
            }
        }

        /// emitWickCoordinate checks the differentiated boundary pole.
        pub fn emitWickCoordinate(self: *@This(), factor: anytype) !void {
            self.coordinate_count += 1;
            if (factor.scalar.numerator != 2 or factor.scalar.denominator != 1) return error.UnexpectedCoordinateScalar;
            switch (factor.kernel) {
                .difference_power => |power| {
                    if (power.coordinate.left != self.expected_y or power.coordinate.right != self.expected_y2 or power.exponent != -3) return error.UnexpectedCoordinateFactor;
                    self.saw_coordinate = true;
                },
                else => return error.UnexpectedCoordinateFactor,
            }
        }

        /// emitWickTensor checks that the Neumann projector resolves from config.
        pub fn emitWickTensor(self: *@This(), factor: anytype) !void {
            self.tensor_count += 1;
            switch (factor) {
                .projector_metric => |projector_metric| switch (projector_metric.projector) {
                    .config => |value| switch (value) {
                        .tensor_projector => |projector| {
                            if (@intFromEnum(projector) != self.expected_neumann) return error.UnexpectedProjectorConfig;
                            self.saw_projector = true;
                        },
                        else => return error.UnexpectedProjectorConfig,
                    },
                    else => return error.UnexpectedProjectorSource,
                },
                else => return error.UnexpectedTensorFactor,
            }
        }

        /// emitWickAction counts unexpected profile actions.
        pub fn emitWickAction(self: *@This(), factor: anytype) !void {
            _ = factor;
            self.action_count += 1;
        }

        /// emitWickTermEnd accepts the completed boundary term.
        pub fn emitWickTermEnd(self: *@This()) !void {
            _ = self;
        }
    };

    var sink = Sink{
        .expected_y = @intFromEnum(y),
        .expected_y2 = @intFromEnum(y2),
        .expected_neumann = @intFromEnum(neumann),
    };
    try testing.expectEqual(@as(usize, 1), try shared.emitWickPairTerms(&Disk.config.disk, ops, 0, 1, &sink));
    try testing.expectEqual(@as(usize, 1), sink.term_count);
    try testing.expectEqual(@as(usize, 1), sink.scalar_count);
    try testing.expectEqual(@as(usize, 1), sink.coordinate_count);
    try testing.expectEqual(@as(usize, 1), sink.tensor_count);
    try testing.expectEqual(@as(usize, 0), sink.action_count);
    try testing.expect(sink.saw_scalar);
    try testing.expect(sink.saw_coordinate);
    try testing.expect(sink.saw_projector);
}
