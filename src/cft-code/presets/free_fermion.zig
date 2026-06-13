const std = @import("std");
const generated_fixtures = @import("../correlators/generated_fixtures.zig");
const shared = @import("shared.zig");

const Handle = shared.Handle;
const Builder = *shared.Local;
const Operator = *shared.LocalOperator;

const FreeFermionSphereConfig = struct {
    dimension: u16,
    include_antiholomorphic_copy: bool = true,
};

/// freeFermionSphere builds the generated preset type for sphere NS free fermions.
pub fn freeFermionSphere(comptime cfg: FreeFermionSphereConfig) type {
    if (cfg.dimension == 0) @compileError("free-fermion target dimension must be nonzero");
    if (cfg.dimension != 10) @compileError("freeFermionSphere exposes generated fixtures only; instantiate the Lisp free-fermion template for this dimension and regenerate");
    return if (cfg.include_antiholomorphic_copy) GeneratedFreeFermionSphere10Full else GeneratedFreeFermionSphere10;
}

const GeneratedFreeFermionSphere10 = struct {
    const Base = generated_fixtures.FreeFermion;

    /// op exposes descriptor-generated NS free-fermion local operator builders.
    pub const op = struct {
        /// psi builds a holomorphic NS free-fermion insertion.
        pub fn psi(builder: anytype, mu: anytype, n: u8, z: Handle.Coord) !Operator {
            comptime shared.assertTargetIndexHandle(@TypeOf(mu));
            return Base.field("psi").localSingle(builder, z, n, .{mu});
        }
    };
    /// config exposes descriptor-generated correlator configs for this preset.
    pub const config = Base.config;
    /// basis streams descriptor-generated compact NS free-fermion mode words.
    pub const basis = Base.basis;
    /// text exposes bounded result-inspection sinks.
    pub const text = Base.text;

    /// local constructs a label-preserving local-operator builder.
    pub fn local(allocator: std.mem.Allocator) !Builder {
        return shared.Local.init(allocator);
    }

    /// correlator streams descriptor-generated rule matches for NS free-fermion insertions.
    pub fn correlator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
        return shared.streamCorrelator(config_ptr, ops, sink);
    }
};

const GeneratedFreeFermionSphere10Full = struct {
    const Base = generated_fixtures.FreeFermion10Full;

    /// op exposes descriptor-generated NS free-fermion local operator builders.
    pub const op = struct {
        /// psi builds a holomorphic NS free-fermion insertion.
        pub fn psi(builder: anytype, mu: anytype, n: u8, z: Handle.Coord) !Operator {
            comptime shared.assertTargetIndexHandle(@TypeOf(mu));
            return Base.field("psi").localSingle(builder, z, n, .{mu});
        }

        /// psit builds an antiholomorphic NS free-fermion insertion.
        pub fn psit(builder: anytype, mu: anytype, n: u8, zbar: Handle.Coord) !Operator {
            comptime shared.assertTargetIndexHandle(@TypeOf(mu));
            return Base.field("psit").localSingle(builder, zbar, n, .{mu});
        }
    };
    /// config exposes descriptor-generated correlator configs for this preset.
    pub const config = Base.config;
    /// basis streams descriptor-generated compact NS free-fermion mode words.
    pub const basis = Base.basis;
    /// text exposes bounded result-inspection sinks.
    pub const text = Base.text;

    /// local constructs a label-preserving local-operator builder.
    pub fn local(allocator: std.mem.Allocator) !Builder {
        return shared.Local.init(allocator);
    }

    /// correlator streams descriptor-generated rule matches for NS free-fermion insertions.
    pub fn correlator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
        return shared.streamCorrelator(config_ptr, ops, sink);
    }
};
