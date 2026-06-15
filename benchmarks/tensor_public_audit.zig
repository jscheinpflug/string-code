const std = @import("std");
const tensor = @import("tensor-code");

fn nowNs() u128 {
    var ts: std.os.linux.timespec = undefined;
    _ = std.os.linux.clock_gettime(.MONOTONIC, &ts);
    return @as(u128, @intCast(ts.sec)) * std.time.ns_per_s + @as(u128, @intCast(ts.nsec));
}

const AuditSink = struct {
    term_count: u64 = 0,
    atom_count: u64 = 0,
    compact_atom_count: u64 = 0,

    pub fn emitTerm(self: *AuditSink, term: tensor.SymbolicTerm) !void {
        self.term_count += 1;
        self.atom_count += term.atoms.len;
        for (term.atoms) |atom| {
            switch (atom) {
                .metric_pair,
                .vector_slot_delta,
                .vector_slot_metric,
                .gamma_matrix,
                .gamma_form,
                .gamma_action,
                .spinor_pair,
                .structure_constant,
                .generalized_delta,
                .epsilon,
                .hodge_star,
                .antisymmetrizer,
                .identity_route,
                .spinor_index_delta,
                .exterior_gamma_action,
                .form_rank_split_delta,
                .tensor_form_spinor_pair,
                .clifford_product_factor,
                => {},
                else => self.compact_atom_count += 1,
            }
        }
    }
};

fn printHeader() void {
    std.debug.print(
        "engine\tcase\tbasis\tpaths\tfully_expandable\tmissing\tprimitive_terms\tprimitive_atoms\tcompact_atoms\tpage_budget_terms\tbudget_terms\tns\tstatus\n",
        .{},
    );
}

fn printPhase(name: []const u8, start: u128) void {
    std.debug.print("tensor-public-phase\t{s}\t{}\n", .{ name, nowNs() - start });
}

fn runSo10HookSix() !void {
    const start = nowNs();
    var ctx = try tensor.Context.init(std.heap.page_allocator);
    defer ctx.deinit();

    const so10 = try ctx.registerAlgebra(.{ .simple = .{ .family = .d, .rank = 5 } });
    const hook = try ctx.registerIrrep(so10, .{ .dynkin = &.{ 1, 1, 0, 0, 0 } });
    printPhase("registered", start);
    const hook_leg = tensor.ExternalLeg.primitive(hook, &.{
        .init(.custom, "H"),
    });
    const basis = try ctx.invariantBasis(.{
        .algebra = so10,
        .external_legs = &.{ hook_leg, hook_leg, hook_leg, hook_leg, hook_leg, hook_leg },
    });
    printPhase("basis", start);
    const basis_count = ctx.basisInvariantCount(basis) orelse 0;
    const coverage = try ctx.basisFormulaCoverageAudit(basis);
    printPhase("coverage", start);

    var primitive_sink: AuditSink = .{};
    _ = try ctx.renderInvariantFiltered(basis, tensor.InvariantHandle.init(16944), .{
        .projectors = .expanded_terms,
        .max_terms = 1,
    }, tensor.ExpansionFilter.acceptAll(), &primitive_sink);
    const primitive_atoms = primitive_sink.atom_count - primitive_sink.compact_atom_count;
    const primitive_ok = primitive_sink.term_count == 1 and primitive_atoms != 0 and primitive_sink.compact_atom_count == 0;
    printPhase("primitive-render", start);

    ctx.setTensorOnlyResourcePolicy(.{ .term_pair_work_limit = 0 });
    var page_budget_sink: AuditSink = .{};
    const page_budget_ok = blk: {
        _ = ctx.renderInvariantFiltered(basis, tensor.InvariantHandle.init(0), .{
            .projectors = .expanded_terms,
            .max_terms = 1,
        }, tensor.ExpansionFilter.acceptAll(), &page_budget_sink) catch |err| {
            break :blk err == error.TensorResourceBudgetExceeded;
        };
        break :blk false;
    };
    printPhase("page-budget-render", start);

    ctx.setTensorOnlyResourcePolicy(.{ .output_term_count_limit = 0 });
    var sink: AuditSink = .{};
    const budget_ok = blk: {
        _ = ctx.renderInvariantFiltered(basis, tensor.InvariantHandle.init(0), .{ .projectors = .expanded_terms }, tensor.ExpansionFilter.acceptAll(), &sink) catch |err| {
            break :blk err == error.TensorResourceBudgetExceeded;
        };
        break :blk false;
    };
    printPhase("budget-render", start);

    const ok = basis_count == 16945 and
        coverage.path_count == 16945 and
        coverage.fully_expandable_path_count == 16945 and
        coverage.missing_step_count == 0 and
        coverage.first_missing_projector == null and
        primitive_ok and
        page_budget_ok and
        page_budget_sink.term_count == 0 and
        budget_ok and
        sink.term_count == 0;

    std.debug.print(
        "tensor-public\tpublic-so10-hook6\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{s}\n",
        .{
            basis_count,
            coverage.path_count,
            coverage.fully_expandable_path_count,
            coverage.missing_step_count,
            primitive_sink.term_count,
            primitive_atoms,
            primitive_sink.compact_atom_count,
            page_budget_sink.term_count,
            sink.term_count,
            nowNs() - start,
            if (ok) "ok" else "failed",
        },
    );
    if (!ok) return error.PublicHookSixRegressionFailed;
}

pub fn main(init: std.process.Init) !void {
    var args = std.process.Args.Iterator.init(init.minimal.args);
    _ = args.next();
    const filter = args.next() orelse "public-so10-hook6";
    printHeader();
    if (std.mem.eql(u8, filter, "public-so10-hook6")) {
        try runSo10HookSix();
        return;
    }
    return error.UnknownPublicAuditCase;
}
