const std = @import("std");

/// build defines the checked library modules and their test steps.
pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const tensor_mod = b.addModule("tensor-code", .{
        .root_source_file = b.path("src/tensor-code/tensor-code.zig"),
        .target = target,
        .optimize = optimize,
    });

    const cft_mod = b.addModule("cft-code", .{
        .root_source_file = b.path("src/cft-code/cft-code.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "tensor-code", .module = tensor_mod },
        },
    });

    const nlsm_mod = b.addModule("nlsm-code", .{
        .root_source_file = b.path("src/nlsm-code/nlsm-code.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "cft-code", .module = cft_mod },
        },
    });

    const root_mod = b.addModule("string-code", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "tensor-code", .module = tensor_mod },
            .{ .name = "cft-code", .module = cft_mod },
            .{ .name = "nlsm-code", .module = nlsm_mod },
        },
    });

    const cft_kernel_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/cft-code/kernel.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "tensor-code", .module = tensor_mod },
            },
        }),
    });
    const run_cft_kernel_tests = b.addRunArtifact(cft_kernel_tests);

    const root_tests = b.addTest(.{
        .root_module = root_mod,
    });
    const run_root_tests = b.addRunArtifact(root_tests);

    const nlsm_tests = b.addTest(.{
        .root_module = nlsm_mod,
    });
    const run_nlsm_tests = b.addRunArtifact(nlsm_tests);

    const generated_abi_mod = b.createModule(.{
        .root_source_file = b.path("src/cft-code/generated_abi.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
        .imports = &.{
            .{ .name = "tensor-code", .module = tensor_mod },
        },
    });
    const generated_abi_tests = b.addTest(.{
        .root_module = generated_abi_mod,
    });
    const run_generated_abi_tests = b.addRunArtifact(generated_abi_tests);

    const generated_abi_lib = b.addLibrary(.{
        .name = "string_code_cft_generated",
        .root_module = generated_abi_mod,
        .linkage = .dynamic,
    });
    b.installArtifact(generated_abi_lib);

    const run_basis_generation_bench = addBasisGenerationRun(b, target, optimize, "basis_generation_compact", "benchmarks/basis_generation_compact.zig");
    const run_basis_generation_compare = addBasisGenerationRun(b, target, optimize, "basis_generation_bc_compare", "benchmarks/basis_generation_bc_compare.zig");
    const run_basis_generation_deep_bench = addBasisGenerationRun(b, target, optimize, "basis_generation_deep_bench", "benchmarks/basis_generation_deep_bench.zig");
    const run_basis_generation_operator_bench = addBasisGenerationRun(b, target, optimize, "basis_generation_operator_bench", "benchmarks/basis_generation_operator_bench.zig");

    b.default_step.dependOn(&run_cft_kernel_tests.step);
    b.default_step.dependOn(&run_root_tests.step);
    b.default_step.dependOn(&run_nlsm_tests.step);
    b.default_step.dependOn(&run_generated_abi_tests.step);

    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&run_cft_kernel_tests.step);
    test_step.dependOn(&run_root_tests.step);
    test_step.dependOn(&run_nlsm_tests.step);
    test_step.dependOn(&run_generated_abi_tests.step);

    const test_nlsm_step = b.step("test-nlsm", "Run nlsm-code tests");
    test_nlsm_step.dependOn(&run_nlsm_tests.step);

    const basis_bench_step = b.step("basis-bench", "Run compact basis-generation benchmark");
    basis_bench_step.dependOn(&run_basis_generation_bench.step);

    const basis_compare_step = b.step("basis-compare", "Print compact b/c basis-generation comparison fixtures");
    basis_compare_step.dependOn(&run_basis_generation_compare.step);

    const basis_deep_bench_step = b.step("basis-deep-bench", "Run broad compact basis-generation benchmark");
    basis_deep_bench_step.dependOn(&run_basis_generation_deep_bench.step);

    const basis_operator_bench_step = b.step("basis-operator-bench", "Run direct operator basis-generation benchmark");
    basis_operator_bench_step.dependOn(&run_basis_generation_operator_bench.step);
}

fn addBasisGenerationRun(
    b: *std.Build,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    name: []const u8,
    source_path: []const u8,
) *std.Build.Step.Run {
    const exe = b.addExecutable(.{
        .name = name,
        .root_module = b.createModule(.{
            .root_source_file = b.path(source_path),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{
                    .name = "basis-generation",
                    .module = b.createModule(.{
                        .root_source_file = b.path("src/cft-code/basis-generation/basis-generation.zig"),
                        .target = target,
                        .optimize = optimize,
                    }),
                },
            },
        }),
    });
    return b.addRunArtifact(exe);
}
