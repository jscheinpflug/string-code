const std = @import("std");
const basis_generation = @import("../basis-generation/basis-generation.zig");
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

fn productQuantumCount(comptime factors: anytype) usize {
    var count: usize = 0;
    inline for (factors) |Factor| count += Factor.basis.quantum_schema.len;
    return count;
}

fn productQuantumSchema(comptime factors: anytype) [productQuantumCount(factors)]basis_generation.Quantum {
    var schema: [productQuantumCount(factors)]basis_generation.Quantum = undefined;
    var offset: usize = 0;
    inline for (factors) |Factor| {
        inline for (Factor.basis.quantum_schema) |quantum| {
            schema[offset] = quantum;
            offset += 1;
        }
    }
    return schema;
}

fn productModeCapacity(comptime factors: anytype, comptime max_level_ticks: u32) usize {
    var count: usize = 0;
    inline for (factors) |Factor| count += Factor.basis.modeCapacity(max_level_ticks);
    return count;
}

fn productSeedCapacity(comptime factors: anytype) usize {
    var count: usize = 1;
    inline for (factors) |Factor| count *= Factor.basis.seedCapacity();
    return count;
}

fn productRenderModeCount(comptime factors: anytype) usize {
    var count: usize = 0;
    inline for (factors) |Factor| count += Factor.basis.render_table.modes.len;
    return count;
}

fn basisSeedBitWidth(comptime Basis: type) usize {
    var width: usize = 0;
    inline for (Basis.render_table.seed_bits) |atom| {
        width = @max(width, @as(usize, @intCast(atom.id)) + 1);
    }
    return width;
}

fn productRenderSeedBitCount(comptime factors: anytype) usize {
    var count: usize = 0;
    inline for (factors) |Factor| count += Factor.basis.render_table.seed_bits.len;
    return count;
}

fn productRenderModes(comptime factors: anytype) [productRenderModeCount(factors)]basis_generation.RenderAtom {
    var modes: [productRenderModeCount(factors)]basis_generation.RenderAtom = undefined;
    var offset: usize = 0;
    inline for (factors, 0..) |Factor, component| {
        inline for (Factor.basis.render_table.modes) |atom| {
            var product_atom = atom;
            product_atom.component = component;
            modes[offset] = product_atom;
            offset += 1;
        }
    }
    return modes;
}

fn productRenderSeedBits(comptime factors: anytype) [productRenderSeedBitCount(factors)]basis_generation.RenderAtom {
    var seed_bits: [productRenderSeedBitCount(factors)]basis_generation.RenderAtom = undefined;
    var offset: usize = 0;
    var bit_offset: usize = 0;
    inline for (factors, 0..) |Factor, component| {
        inline for (Factor.basis.render_table.seed_bits) |atom| {
            var product_atom = atom;
            product_atom.id = @intCast(bit_offset + atom.id);
            product_atom.component = component;
            seed_bits[offset] = product_atom;
            offset += 1;
        }
        bit_offset += basisSeedBitWidth(Factor.basis);
    }
    return seed_bits;
}

fn shiftedSeedBody(body: u32, offset: usize) !u32 {
    if (offset == 0) return body;
    var shifted: u32 = 0;
    for (0..32) |bit| {
        if ((body & (@as(u32, 1) << @intCast(bit))) == 0) continue;
        if (bit + offset >= 32) return error.InvalidDescriptor;
        shifted |= @as(u32, 1) << @intCast(bit + offset);
    }
    return shifted;
}

fn ProductBasis(comptime factors: anytype) type {
    const quantum_schema_storage = productQuantumSchema(factors);
    const render_modes_storage = productRenderModes(factors);
    const render_seed_bits_storage = productRenderSeedBits(factors);
    return struct {
        /// quantum_schema concatenates the factor quantum vectors.
        pub const quantum_schema = quantum_schema_storage;
        /// render_table preserves factor render names with component tags.
        pub const render_table = basis_generation.RenderTable{ .modes = &render_modes_storage, .seed_bits = &render_seed_bits_storage };

        /// modeCapacity returns the merged mode-band capacity for all factors.
        pub fn modeCapacity(comptime max_level_ticks: u32) usize {
            return productModeCapacity(factors, max_level_ticks);
        }

        /// seedCapacity returns the finite product-primary seed capacity.
        pub fn seedCapacity() usize {
            return productSeedCapacity(factors);
        }

        fn writeModes(comptime max_level_ticks: u32, modes: []basis_generation.Mode, quantum_storage: []i32) ![]const basis_generation.Mode {
            var mode_offset: usize = 0;
            var quantum_offset: usize = 0;
            inline for (factors, 0..) |Factor, component| {
                const local_capacity = Factor.basis.modeCapacity(max_level_ticks);
                const written = try Factor.basis.writeModes(
                    max_level_ticks,
                    @intCast(component),
                    quantum_offset,
                    quantum_schema.len,
                    modes[mode_offset .. mode_offset + local_capacity],
                    quantum_storage[mode_offset * quantum_schema.len ..],
                );
                mode_offset += written.len;
                quantum_offset += Factor.basis.quantum_schema.len;
            }
            return modes[0..mode_offset];
        }

        fn writeSeeds(seeds: []basis_generation.Seed, quantum_storage: []i32, component_weight_storage: []i32) ![]const basis_generation.Seed {
            if (seeds.len < seedCapacity() or quantum_storage.len < seedCapacity() * quantum_schema.len) return error.ContextTooSmall;
            if (component_weight_storage.len < seedCapacity() * factors.len) return error.ContextTooSmall;
            @memset(quantum_storage[0..quantum_schema.len], 0);
            @memset(component_weight_storage[0..factors.len], 0);
            seeds[0] = .{
                .quantum_values = quantum_storage[0..quantum_schema.len],
                .component_weight_ticks = component_weight_storage[0..factors.len],
            };

            var current_count: usize = 1;
            var quantum_offset: usize = 0;
            var seed_body_offset: usize = 0;
            inline for (factors, 0..) |Factor, component| {
                var factor_seeds_storage: [Factor.basis.seedCapacity()]basis_generation.Seed = undefined;
                var factor_quantum_storage: [Factor.basis.seedCapacity() * Factor.basis.quantum_schema.len]i32 = undefined;
                const factor_seeds = try Factor.basis.writeSeeds(0, Factor.basis.quantum_schema.len, &factor_seeds_storage, &factor_quantum_storage);

                var old_index = current_count;
                while (old_index > 0) {
                    old_index -= 1;
                    var old_quantum: [quantum_schema.len]i32 = undefined;
                    const old_slice = seeds[old_index].quantum_values;
                    for (0..quantum_schema.len) |slot| old_quantum[slot] = old_slice[slot];
                    var old_component_weights: [factors.len]i32 = undefined;
                    const old_component_slice = seeds[old_index].component_weight_ticks;
                    for (0..factors.len) |slot| old_component_weights[slot] = old_component_slice[slot];
                    const old_weight = seeds[old_index].weight_ticks;
                    const old_body = seeds[old_index].body;

                    for (factor_seeds, 0..) |factor_seed, factor_index| {
                        const next_index = old_index * factor_seeds.len + factor_index;
                        const next_quantum = quantum_storage[next_index * quantum_schema.len .. (next_index + 1) * quantum_schema.len];
                        for (0..quantum_schema.len) |slot| next_quantum[slot] = old_quantum[slot];
                        for (factor_seed.quantum_values, 0..) |value, local_slot| next_quantum[quantum_offset + local_slot] += value;
                        const next_component_weights = component_weight_storage[next_index * factors.len .. (next_index + 1) * factors.len];
                        for (0..factors.len) |slot| next_component_weights[slot] = old_component_weights[slot];
                        next_component_weights[component] += factor_seed.weight_ticks;
                        seeds[next_index] = .{
                            .id = @intCast(next_index),
                            .weight_ticks = old_weight + factor_seed.weight_ticks,
                            .component_weight_ticks = next_component_weights,
                            .quantum_values = next_quantum,
                            .body = old_body | try shiftedSeedBody(factor_seed.body, seed_body_offset),
                        };
                    }
                }
                current_count *= factor_seeds.len;
                quantum_offset += Factor.basis.quantum_schema.len;
                seed_body_offset += basisSeedBitWidth(Factor.basis);
            }
            return seeds[0..current_count];
        }

        /// stream enumerates compact product words through one merged traversal.
        pub fn stream(comptime max_level_ticks: u32, comptime max_depth: usize, query: basis_generation.Query, sink: anytype) !void {
            var modes_storage: [modeCapacity(max_level_ticks)]basis_generation.Mode = undefined;
            var mode_quantum_storage: [modeCapacity(max_level_ticks) * quantum_schema.len]i32 = undefined;
            const modes = try writeModes(max_level_ticks, &modes_storage, &mode_quantum_storage);
            var seeds_storage: [seedCapacity()]basis_generation.Seed = undefined;
            var seed_quantum_storage: [seedCapacity() * quantum_schema.len]i32 = undefined;
            var seed_component_weight_storage: [seedCapacity() * factors.len]i32 = undefined;
            const seeds = try writeSeeds(&seeds_storage, &seed_quantum_storage, &seed_component_weight_storage);
            var storage = basis_generation.StackContextWithComponents(modes_storage.len, max_level_ticks, quantum_schema.len, max_depth, factors.len){};
            var context = storage.context();
            return basis_generation.stream(.{
                .quantum_schema = &quantum_schema,
                .modes = modes,
                .seeds = seeds,
            }, query, &context, sink);
        }
    };
}

/// product builds the generated preset type for a product of independent bulk presets.
pub fn product(comptime factors: anytype) type {
    return struct {
        /// op is intentionally empty; use the factor builders passed to product.
        pub const op = struct {};
        /// config exposes named correlator configs for this product preset.
        pub const config = ProductCorrelatorConfig(factors);
        /// basis streams compact product states without materialized factor bases.
        pub const basis = ProductBasis(factors);
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
