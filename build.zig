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

    const root_mod = b.addModule("string-code", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "tensor-code", .module = tensor_mod },
            .{ .name = "cft-code", .module = cft_mod },
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

    b.default_step.dependOn(&run_cft_kernel_tests.step);
    b.default_step.dependOn(&run_root_tests.step);

    const test_step = b.step("test", "Run library tests");
    test_step.dependOn(&run_cft_kernel_tests.step);
    test_step.dependOn(&run_root_tests.step);
}
