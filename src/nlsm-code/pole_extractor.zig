const std = @import("std");
const geometry = @import("local_geometry_reducer.zig");
const scheme = @import("scheme.zig");
const counterterms = @import("counterterms.zig");

/// KernelTermRow is one reduced local branch before pole extraction.
pub const KernelTermRow = struct {
    scheme: scheme.DimRegMS,
    local_operator: counterterms.LocalCountertermKind,
    target_flavor: geometry.GeometryFlavor = .generic_riemannian,
    alpha_prime_power: i16 = 0,
    combinatorial: counterterms.Rational = .{ .numerator = 1, .denominator = 1 },
    kernel: counterterms.KernelSignature,
    term: geometry.TensorTerm,
};

/// LocalityClass records whether one master family contributes a local pole.
pub const LocalityClass = enum(u8) {
    local,
    non_local,
    scaleless,
};

/// PoleResidue stores one Laurent-coefficient contribution for a matched rule.
pub const PoleResidue = struct {
    pole_order: u8,
    residue: counterterms.Rational,
};

/// KernelPoleRule maps one reduced kernel signature to local pole data.
pub const KernelPoleRule = struct {
    signature: counterterms.KernelSignature,
    locality: LocalityClass = .local,
    residues: []const PoleResidue = &.{},
};

/// PoleExtractionSummary reports how the kernel rows were classified.
pub const PoleExtractionSummary = struct {
    emitted_pole_count: usize = 0,
    scaleless_count: u32 = 0,
    non_local_count: u32 = 0,
    unmatched_count: u32 = 0,
};

fn sameSignature(left: counterterms.KernelSignature, right: counterterms.KernelSignature) bool {
    return left.family == right.family and
        left.loop_order == right.loop_order and
        left.propagator_len == right.propagator_len and
        left.numerator_rank == right.numerator_rank and
        left.external_derivative_order == right.external_derivative_order and
        std.mem.eql(u8, left.propagator_powers[0..], right.propagator_powers[0..]);
}

fn findRule(rules: []const KernelPoleRule, signature: counterterms.KernelSignature) ?KernelPoleRule {
    for (rules) |rule| {
        if (sameSignature(rule.signature, signature)) return rule;
    }
    return null;
}

/// extractPoleRows matches reduced kernel signatures to explicit local pole rules.
pub fn extractPoleRows(rows: []const KernelTermRow, rules: []const KernelPoleRule, output: []counterterms.PoleRow) !PoleExtractionSummary {
    var summary = PoleExtractionSummary{};

    for (rows) |row| {
        if (row.kernel.isScaleless()) {
            summary.scaleless_count += 1;
            continue;
        }

        const rule = findRule(rules, row.kernel) orelse {
            summary.unmatched_count += 1;
            continue;
        };

        switch (rule.locality) {
            .scaleless => {
                summary.scaleless_count += 1;
                continue;
            },
            .non_local => {
                summary.non_local_count += 1;
                continue;
            },
            .local => {},
        }

        for (rule.residues) |residue| {
            if (summary.emitted_pole_count == output.len) return error.OutputTooSmall;
            output[summary.emitted_pole_count] = .{
                .scheme = row.scheme,
                .local_operator = row.local_operator,
                .target_flavor = row.target_flavor,
                .loop_order = row.kernel.loop_order,
                .pole_order = residue.pole_order,
                .alpha_prime_power = row.alpha_prime_power,
                .residue = try row.combinatorial.mul(residue.residue),
                .kernel = row.kernel,
                .term = row.term,
            };
            summary.emitted_pole_count += 1;
        }
    }

    return summary;
}

const bubble_residues = [_]PoleResidue{
    .{ .pole_order = 1, .residue = .{ .numerator = 1, .denominator = 1 } },
};

const nested_bubble_residues = [_]PoleResidue{
    .{ .pole_order = 2, .residue = .{ .numerator = 1, .denominator = 2 } },
    .{ .pole_order = 1, .residue = .{ .numerator = 3, .denominator = 2 } },
};

const bootstrap_rules = [_]KernelPoleRule{
    .{
        .signature = .{
            .family = .scaleless_tadpole,
            .loop_order = 1,
        },
        .locality = .scaleless,
    },
    .{
        .signature = .{
            .family = .bubble,
            .loop_order = 1,
            .propagator_len = 2,
            .propagator_powers = [_]u8{ 1, 1, 0, 0, 0, 0, 0, 0 },
            .external_derivative_order = 2,
        },
        .residues = &bubble_residues,
    },
    .{
        .signature = .{
            .family = .nested_bubble,
            .loop_order = 2,
            .propagator_len = 4,
            .propagator_powers = [_]u8{ 1, 1, 1, 1, 0, 0, 0, 0 },
            .external_derivative_order = 2,
        },
        .residues = &nested_bubble_residues,
    },
};

/// stringbookBootstrapRules returns the first explicit rule table used for low-loop checks.
pub fn stringbookBootstrapRules() []const KernelPoleRule {
    return &bootstrap_rules;
}

test "pole extractor emits local rows from matched signatures" {
    const testing = std.testing;
    const slots = [_]geometry.TensorSlot{
        .{ .id = 1, .sort = .real_tangent },
        .{ .id = 2, .sort = .real_tangent },
        .{ .id = 3, .sort = .real_tangent },
        .{ .id = 4, .sort = .real_tangent },
    };
    const atoms = [_]geometry.TensorAtom{.{ .kind = .riemann, .slots = &slots }};
    const rows = [_]KernelTermRow{.{
        .scheme = scheme.stringbookMS(),
        .local_operator = .metric_beta,
        .alpha_prime_power = 1,
        .kernel = .{
            .family = .bubble,
            .loop_order = 1,
            .propagator_len = 2,
            .propagator_powers = [_]u8{ 1, 1, 0, 0, 0, 0, 0, 0 },
            .external_derivative_order = 2,
        },
        .term = .{ .atoms = &atoms },
    }};

    var output: [2]counterterms.PoleRow = undefined;
    const summary = try extractPoleRows(&rows, stringbookBootstrapRules(), &output);
    try testing.expectEqual(@as(usize, 1), summary.emitted_pole_count);
    try testing.expectEqual(@as(u8, 1), output[0].pole_order);
    try testing.expectEqual(counterterms.LocalCountertermKind.metric_beta, output[0].local_operator);
}

test "pole extractor preserves calabi-yau target flavor for later quotients" {
    const testing = std.testing;
    const slots = [_]geometry.TensorSlot{
        .{ .id = 1, .sort = .holomorphic_tangent },
        .{ .id = 2, .sort = .antiholomorphic_tangent },
    };
    const atoms = [_]geometry.TensorAtom{.{ .kind = .ricci, .slots = &slots }};
    const rows = [_]KernelTermRow{.{
        .scheme = scheme.stringbookMS(),
        .local_operator = .kahler_potential_beta,
        .target_flavor = .calabi_yau,
        .alpha_prime_power = 3,
        .kernel = .{
            .family = .nested_bubble,
            .loop_order = 2,
            .propagator_len = 4,
            .propagator_powers = [_]u8{ 1, 1, 1, 1, 0, 0, 0, 0 },
            .external_derivative_order = 2,
        },
        .term = .{ .atoms = &atoms },
    }};

    var output: [4]counterterms.PoleRow = undefined;
    const summary = try extractPoleRows(&rows, stringbookBootstrapRules(), &output);
    try testing.expectEqual(@as(usize, 2), summary.emitted_pole_count);
    try testing.expectEqual(geometry.GeometryFlavor.calabi_yau, output[0].target_flavor);
    try testing.expectEqual(counterterms.LocalCountertermKind.kahler_potential_beta, output[0].local_operator);
}

test "pole extractor drops scaleless signatures and reports unmatched rows" {
    const testing = std.testing;
    const rows = [_]KernelTermRow{
        .{
            .scheme = scheme.stringbookMS(),
            .local_operator = .metric_beta,
            .kernel = .{ .family = .scaleless_tadpole, .loop_order = 1 },
            .term = .{},
        },
        .{
            .scheme = scheme.stringbookMS(),
            .local_operator = .metric_beta,
            .kernel = .{ .family = .ladder, .loop_order = 4 },
            .term = .{},
        },
    };

    var output: [1]counterterms.PoleRow = undefined;
    const summary = try extractPoleRows(&rows, stringbookBootstrapRules(), &output);
    try testing.expectEqual(@as(u32, 1), summary.scaleless_count);
    try testing.expectEqual(@as(u32, 1), summary.unmatched_count);
    try testing.expectEqual(@as(usize, 0), summary.emitted_pole_count);
}
