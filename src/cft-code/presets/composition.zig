const std = @import("std");
const shared = @import("shared.zig");
const declare = shared.declare;

const Builder = *shared.Local;

fn ProductCorrelatorConfig(comptime factors: anytype) type {
    const merged = declare.mergeSphereConfigs(factors);
    return struct {
        /// sphere selects composed product Wick and zero-mode rules.
        pub const sphere = merged.config;
    };
}

/// product builds the generated preset type for a product of independent bulk presets.
pub fn product(comptime factors: anytype) type {
    return struct {
        /// op is intentionally empty; use the factor builders passed to product.
        pub const op = struct {};
        /// config exposes named correlator configs for this product preset.
        pub const config = ProductCorrelatorConfig(factors);
        /// text exposes bounded result-inspection sinks.
        pub const text = shared.text;
        /// local constructs a label-preserving local-operator builder.
        pub fn local(allocator: std.mem.Allocator) !Builder {
            return shared.Local.init(allocator);
        }

        /// correlator streams rule matches for product-theory insertions.
        pub fn correlator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
            return shared.streamCorrelator(config_ptr, ops, sink);
        }
    };
}

fn BoundaryCorrelatorConfig(comptime Bulk: type, comptime extensions: anytype) type {
    const merged = declare.mergeBoundaryConfig(Bulk, extensions);
    return struct {
        /// disk selects composed boundary Wick and zero-mode rules.
        pub const disk = merged.config;
    };
}

fn BoundaryOp(comptime Bulk: type, comptime extensions: anytype) type {
    _ = extensions;
    return struct {
        /// bulk exposes the bulk operator namespaces.
        pub const bulk = Bulk.op;
    };
}

/// boundary builds the generated preset type for a BCFT from a bulk preset and boundary extensions.
pub fn boundary(comptime Bulk: type, comptime extensions: anytype) type {
    return struct {
        /// op exposes bulk and boundary operator builders.
        pub const op = BoundaryOp(Bulk, extensions);
        /// config exposes named correlator configs for this BCFT.
        pub const config = BoundaryCorrelatorConfig(Bulk, extensions);
        /// text exposes bounded result-inspection sinks.
        pub const text = shared.text;
        /// local constructs a label-preserving local-operator builder.
        pub fn local(allocator: std.mem.Allocator) !Builder {
            return shared.Local.init(allocator);
        }

        /// correlator streams rule matches for BCFT insertions.
        pub fn correlator(config_ptr: anytype, ops: anytype, sink: anytype) !void {
            return shared.streamCorrelator(config_ptr, ops, sink);
        }
    };
}
