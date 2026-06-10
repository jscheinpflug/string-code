const kernel = @import("../kernel.zig");
const normal_ordering = @import("../normal-ordering/normal-ordering.zig");

const PairChoice = struct {
    left: u8,
    right: u8,
    term_index: u16,
    payload: u64 = 0,
};

const default_operator_count = 128;
const no_candidate_index: u16 = 0xffff;

const PairCandidate = struct {
    left: u8,
    right: u8,
    term_index: u16,
    payload: u64,
    residuals: [2]u8,
    residual_count: u8,
    mandatory_before_base: bool,
    next_for_left: u16 = no_candidate_index,
    next_for_right: u16 = no_candidate_index,
};

fn pairDepth(comptime operator_count: usize) usize {
    return operator_count / 2;
}

fn pairCandidateCount(comptime operator_count: usize) usize {
    return (operator_count * (operator_count - 1)) / 2;
}

fn tacticOperatorCount(comptime Tactic: type) comptime_int {
    return if (@hasDecl(Tactic, "traversal_operator_count")) Tactic.traversal_operator_count else default_operator_count;
}

fn Scratch(comptime operator_count: usize) type {
    return struct {
        residual_indices: [operator_count]usize = undefined,
        pair_stack: [pairDepth(operator_count)]PairChoice = undefined,
        candidates: [pairCandidateCount(operator_count)]PairCandidate = undefined,
        first_candidate_by_operator: [operator_count]u16 = undefined,
        last_candidate_by_operator: [operator_count]u16 = undefined,
        first_candidate_by_left: [operator_count]u16 = undefined,
        end_candidate_by_left: [operator_count]u16 = undefined,
        zero_mode_survivable: [operator_count]bool = undefined,
        zero_mode_forced_mask: u128 = undefined,
        parities: [operator_count]bool = undefined,
        parity_mask: u128 = undefined,

        pub fn init() @This() {
            return .{};
        }
    };
}

const NullSink = struct {
    /// emitWickTermStart discards a dry-run pair term boundary.
    pub fn emitWickTermStart(_: *@This(), _: anytype) !void {}
    /// emitWickScalar discards a dry-run scalar factor.
    pub fn emitWickScalar(_: *@This(), _: anytype) !void {}
    /// emitWickCoordinate discards a dry-run coordinate factor.
    pub fn emitWickCoordinate(_: *@This(), _: anytype) !void {}
    /// emitWickTensor discards a dry-run tensor factor.
    pub fn emitWickTensor(_: *@This(), _: anytype) !void {}
    /// emitWickAction discards a dry-run action factor.
    pub fn emitWickAction(_: *@This(), _: anytype) !void {}
    /// emitWickTermEnd discards a dry-run pair term end.
    pub fn emitWickTermEnd(_: *@This()) !void {}
    /// emitZeroModeFactor discards a dry-run zero-mode factor.
    pub fn emitZeroModeFactor(_: *@This(), _: anytype) !void {}
    /// emitZeroModeBaseEnd discards a dry-run zero-mode success marker.
    pub fn emitZeroModeBaseEnd(_: *@This()) !void {}
};

fn bit(index: usize) u128 {
    return @as(u128, 1) << @intCast(index);
}

fn initialLiveMask(comptime operator_count: usize, len: usize) u128 {
    if (len == operator_count) return ~@as(u128, 0);
    return bit(len) - 1;
}

fn live(mask: u128, index: usize) bool {
    return (mask & bit(index)) != 0;
}

fn firstLiveIndex(mask: u128) usize {
    const low: u64 = @truncate(mask);
    if (low != 0) return @ctz(low);
    const high: u64 = @truncate(mask >> 64);
    return 64 + @ctz(high);
}

fn residualSlice(scratch: anytype, len: usize, live_mask: u128) []const usize {
    var count: usize = 0;
    var index: usize = 0;
    while (index < len) : (index += 1) {
        if (live(live_mask, index)) {
            scratch.residual_indices[count] = index;
            count += 1;
        }
    }
    return scratch.residual_indices[0..count];
}

fn pairTermCount(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, left: usize, right: usize) !usize {
    if (@hasDecl(Tactic, "pairTermCount")) {
        return Tactic.pairTermCount(config_ptr, ops, left, right);
    }
    var null_sink = NullSink{};
    return Tactic.emitPairTerms(config_ptr, ops, left, right, &null_sink);
}

fn pairTermResiduals(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, left: usize, right: usize, term_index: usize, residuals: *[2]usize) !usize {
    if (@hasDecl(Tactic, "pairTermResiduals")) {
        return Tactic.pairTermResiduals(config_ptr, ops, left, right, term_index, residuals);
    } else {
        return 0;
    }
}

fn pairTermPayload(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, left: usize, right: usize, term_index: usize) !u64 {
    if (@hasDecl(Tactic, "pairTermPayload")) {
        return Tactic.pairTermPayload(config_ptr, ops, left, right, term_index);
    }
    return @intCast(term_index);
}

fn pairTermInfo(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, left: usize, right: usize, term_index: usize, residuals: *[2]usize, payload: *u64, residual_count: *usize) !void {
    if (@hasDecl(Tactic, "pairTermInfo")) {
        return Tactic.pairTermInfo(config_ptr, ops, left, right, term_index, residuals, payload, residual_count);
    }
    payload.* = try pairTermPayload(Tactic, config_ptr, ops, left, right, term_index);
    residual_count.* = try pairTermResiduals(Tactic, config_ptr, ops, left, right, term_index, residuals);
}

fn residualsKeepPair(left: usize, right: usize, residuals: []const usize) bool {
    var keeps_left = false;
    var keeps_right = false;
    for (residuals) |residual| {
        keeps_left = keeps_left or residual == left;
        keeps_right = keeps_right or residual == right;
    }
    return keeps_left and keeps_right;
}

fn appendCandidateForOperator(scratch: anytype, operator_index: usize, candidate_index: u16) void {
    const last = scratch.last_candidate_by_operator[operator_index];
    if (last == no_candidate_index) {
        scratch.first_candidate_by_operator[operator_index] = candidate_index;
    } else if (scratch.candidates[last].left == operator_index) {
        scratch.candidates[last].next_for_left = candidate_index;
    } else {
        scratch.candidates[last].next_for_right = candidate_index;
    }
    scratch.last_candidate_by_operator[operator_index] = candidate_index;
}

fn nextCandidateForOperator(candidate: PairCandidate, operator_index: usize) u16 {
    return if (candidate.left == operator_index) candidate.next_for_left else candidate.next_for_right;
}

fn buildCandidates(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, scratch: anytype) !usize {
    var operator_index: usize = 0;
    while (operator_index < ops.operators.len) : (operator_index += 1) {
        scratch.first_candidate_by_operator[operator_index] = no_candidate_index;
        scratch.last_candidate_by_operator[operator_index] = no_candidate_index;
        scratch.first_candidate_by_left[operator_index] = no_candidate_index;
        scratch.end_candidate_by_left[operator_index] = no_candidate_index;
    }

    var candidate_count: usize = 0;
    var left: usize = 0;
    while (left < ops.operators.len) : (left += 1) {
        const left_start = candidate_count;
        var right = left + 1;
        while (right < ops.operators.len) : (right += 1) {
            if (normal_ordering.same(ops.operators[left], ops.operators[right])) continue;
            const term_count = try pairTermCount(Tactic, config_ptr, ops, left, right);
            var term_index: usize = 0;
            while (term_index < term_count) : (term_index += 1) {
                if (candidate_count == scratch.candidates.len) return error.TooManyWickCandidates;
                var residuals: [2]usize = undefined;
                var payload: u64 = undefined;
                var residual_count: usize = undefined;
                try pairTermInfo(Tactic, config_ptr, ops, left, right, term_index, &residuals, &payload, &residual_count);
                if (residual_count > residuals.len) return error.TooManyWickTermResiduals;
                var compact_residuals: [2]u8 = undefined;
                var residual_index: usize = 0;
                while (residual_index < residual_count) : (residual_index += 1) {
                    compact_residuals[residual_index] = @intCast(residuals[residual_index]);
                }
                const compact_candidate_index: u16 = @intCast(candidate_count);
                scratch.candidates[candidate_count] = .{
                    .left = @intCast(left),
                    .right = @intCast(right),
                    .term_index = @intCast(term_index),
                    .payload = payload,
                    .residuals = compact_residuals,
                    .residual_count = @intCast(residual_count),
                    .mandatory_before_base = residualsKeepPair(left, right, residuals[0..residual_count]),
                };
                appendCandidateForOperator(scratch, left, compact_candidate_index);
                appendCandidateForOperator(scratch, right, compact_candidate_index);
                candidate_count += 1;
            }
        }
        if (candidate_count != left_start) {
            scratch.first_candidate_by_left[left] = @intCast(left_start);
            scratch.end_candidate_by_left[left] = @intCast(candidate_count);
        }
    }
    return candidate_count;
}

fn buildParities(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, scratch: anytype) void {
    scratch.parity_mask = 0;
    var index: usize = 0;
    while (index < ops.operators.len) : (index += 1) {
        const parity = if (@hasDecl(Tactic, "operatorParity")) Tactic.operatorParity(config_ptr, ops, index) else false;
        scratch.parities[index] = parity;
        if (parity) scratch.parity_mask |= bit(index);
    }
}

fn buildZeroModeSurvivability(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, scratch: anytype) void {
    scratch.zero_mode_forced_mask = 0;
    var index: usize = 0;
    while (index < ops.operators.len) : (index += 1) {
        const survivable = operatorCanRemainInZeroMode(Tactic, config_ptr, ops, index);
        scratch.zero_mode_survivable[index] = survivable;
        if (!survivable) scratch.zero_mode_forced_mask |= bit(index);
    }
}

fn pairSign(scratch: anytype, live_mask: u128, left: usize, right: usize) i8 {
    const endpoints = bit(left) | bit(right);
    if ((scratch.parity_mask & endpoints) != endpoints) return 1;
    const below_right = bit(right) - 1;
    const below_or_at_left = bit(left + 1) - 1;
    const between = below_right & ~below_or_at_left;
    const crossings = @popCount(live_mask & scratch.parity_mask & between);
    return if ((crossings & 1) == 0) 1 else -1;
}

fn operatorCanRemainInZeroMode(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, index: usize) bool {
    if (@hasDecl(Tactic, "operatorCanRemainInZeroMode")) {
        return Tactic.operatorCanRemainInZeroMode(config_ptr, ops, index);
    }
    return true;
}

fn firstForcedResidual(scratch: anytype, live_mask: u128) ?usize {
    const forced = live_mask & scratch.zero_mode_forced_mask;
    return if (forced == 0) null else firstLiveIndex(forced);
}

fn zeroModeSucceeds(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, residual: []const usize) !bool {
    if (@hasDecl(Tactic, "zeroModeBaseCaseSucceeds")) {
        return Tactic.zeroModeBaseCaseSucceeds(config_ptr, ops, residual);
    }
    var null_sink = NullSink{};
    return Tactic.emitZeroModeBaseCase(config_ptr, ops, residual, &null_sink);
}

fn emitPairTerm(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, choice: PairChoice, sink: anytype) !void {
    if (@hasDecl(Tactic, "emitPairTermPayload")) {
        try Tactic.emitPairTermPayload(config_ptr, ops, choice.left, choice.right, choice.payload, sink);
        return;
    }
    if (@hasDecl(Tactic, "emitPairTerm")) {
        try Tactic.emitPairTerm(config_ptr, ops, choice.left, choice.right, choice.term_index, sink);
        return;
    }
    if (choice.term_index != 0) return error.InvalidWickTerm;
    if (try Tactic.emitPairTerms(config_ptr, ops, choice.left, choice.right, sink) == 0) {
        return error.InvalidWickBranch;
    }
}

fn emitBranch(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, scratch: anytype, depth: usize, sign: i8, residual: []const usize, sink: anytype) !void {
    if (sign < 0 and @hasDecl(Tactic, "emitBranchSign")) {
        try Tactic.emitBranchSign(config_ptr, sign, sink);
    }

    var index: usize = 0;
    while (index < depth) : (index += 1) {
        try emitPairTerm(Tactic, config_ptr, ops, scratch.pair_stack[index], sink);
    }

    if (!try Tactic.emitZeroModeBaseCase(config_ptr, ops, residual, sink)) {
        return error.InvalidWickBranch;
    }
}

fn pairResultLiveMask(live_mask: u128, candidate: PairCandidate) u128 {
    var next = live_mask & ~bit(candidate.left) & ~bit(candidate.right);
    var residual_index: usize = 0;
    while (residual_index < candidate.residual_count) : (residual_index += 1) {
        next |= bit(candidate.residuals[residual_index]);
    }
    return next;
}

fn pairClearedLiveMask(live_mask: u128, candidate: PairCandidate) u128 {
    return live_mask & ~bit(candidate.left) & ~bit(candidate.right);
}

fn hasMandatoryCandidate(scratch: anytype, live_mask: u128, next_candidate_index: usize, candidate_count: usize) bool {
    var candidate_index = next_candidate_index;
    while (candidate_index < candidate_count) : (candidate_index += 1) {
        const candidate = scratch.candidates[candidate_index];
        if (!candidate.mandatory_before_base) continue;
        if (live(live_mask, candidate.left) and live(live_mask, candidate.right)) return true;
    }
    return false;
}

fn pureFullContraction(scratch: anytype, ops: kernel.Call.MultiOp, candidate_count: usize) bool {
    if ((ops.operators.len & 1) != 0) return false;

    var operator_index: usize = 0;
    while (operator_index < ops.operators.len) : (operator_index += 1) {
        if (scratch.zero_mode_survivable[operator_index]) return false;
    }

    var candidate_index: usize = 0;
    while (candidate_index < candidate_count) : (candidate_index += 1) {
        if (scratch.candidates[candidate_index].residual_count != 0) return false;
    }

    return true;
}

fn pushBranchPairTerm(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, branch: anytype, candidate: PairCandidate) !void {
    try Tactic.pushBranchPairTerm(config_ptr, ops, candidate.left, candidate.right, candidate.payload, branch);
}

fn emitAccumulatedBranch(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, branch: anytype, sign: i8, residual: []const usize, sink: anytype) !void {
    try Tactic.emitAccumulatedBranch(config_ptr, ops, branch, sign, residual, sink);
}

fn emitFullAccumulatedBranch(comptime Tactic: type, config_ptr: *const Tactic.Config, ops: kernel.Call.MultiOp, branch: anytype, sign: i8, sink: anytype) !void {
    if (@hasDecl(Tactic, "emitFullContractionBranch")) {
        try Tactic.emitFullContractionBranch(config_ptr, ops, branch, sign, sink);
        return;
    }
    try Tactic.emitAccumulatedBranch(config_ptr, ops, branch, sign, &.{}, sink);
}

fn walkFullAccumulated(
    comptime Tactic: type,
    config_ptr: *const Tactic.Config,
    ops: kernel.Call.MultiOp,
    scratch: anytype,
    branch: *Tactic.BranchState,
    live_mask: u128,
    depth: usize,
    sign: i8,
    sink: anytype,
) !usize {
    if (live_mask == 0) {
        try emitFullAccumulatedBranch(Tactic, config_ptr, ops, branch, sign, sink);
        return 1;
    }
    if (depth == scratch.pair_stack.len) return 0;

    const first = firstLiveIndex(live_mask);

    var branch_count: usize = 0;
    var candidate_index: usize = scratch.first_candidate_by_left[first];
    const candidate_end: usize = scratch.end_candidate_by_left[first];
    while (candidate_index < candidate_end) : (candidate_index += 1) {
        const candidate = scratch.candidates[candidate_index];

        const left: usize = candidate.left;
        const right: usize = candidate.right;
        if (!live(live_mask, right)) continue;

        const saved = branch.snapshot();
        const next_mask = pairClearedLiveMask(live_mask, candidate);
        const next_sign = sign * pairSign(scratch, live_mask, left, right);
        try pushBranchPairTerm(Tactic, config_ptr, ops, branch, candidate);
        branch_count += try walkFullAccumulated(Tactic, config_ptr, ops, scratch, branch, next_mask, depth + 1, next_sign, sink);
        branch.restore(saved);
    }

    return branch_count;
}

fn walkAccumulated(
    comptime Tactic: type,
    config_ptr: *const Tactic.Config,
    ops: kernel.Call.MultiOp,
    scratch: anytype,
    branch: *Tactic.BranchState,
    live_mask: u128,
    next_candidate_index: usize,
    candidate_count: usize,
    depth: usize,
    sign: i8,
    sink: anytype,
) !usize {
    var branch_count: usize = 0;
    const forced_residual = firstForcedResidual(scratch, live_mask);

    if (forced_residual == null and !hasMandatoryCandidate(scratch, live_mask, next_candidate_index, candidate_count)) {
        const residual = residualSlice(scratch, ops.operators.len, live_mask);
        if (try zeroModeSucceeds(Tactic, config_ptr, ops, residual)) {
            try emitAccumulatedBranch(Tactic, config_ptr, ops, branch, sign, residual, sink);
            branch_count += 1;
        }
    }

    if (depth == scratch.pair_stack.len) return branch_count;

    if (forced_residual) |forced| {
        var candidate_link = scratch.first_candidate_by_operator[forced];
        while (candidate_link != no_candidate_index) {
            const candidate_index: usize = candidate_link;
            const candidate = scratch.candidates[candidate_index];
            candidate_link = nextCandidateForOperator(candidate, forced);
            if (candidate_index < next_candidate_index) continue;
            const left: usize = candidate.left;
            const right: usize = candidate.right;
            if (!live(live_mask, left) or !live(live_mask, right)) continue;

            const saved = branch.snapshot();
            const next_mask = pairResultLiveMask(live_mask, candidate);
            const next_sign = sign * pairSign(scratch, live_mask, left, right);
            try pushBranchPairTerm(Tactic, config_ptr, ops, branch, candidate);
            branch_count += try walkAccumulated(Tactic, config_ptr, ops, scratch, branch, next_mask, candidate_index + 1, candidate_count, depth + 1, next_sign, sink);
            branch.restore(saved);
            if (candidate.mandatory_before_base) return branch_count;
        }
        return branch_count;
    }

    var candidate_index = next_candidate_index;
    while (candidate_index < candidate_count) : (candidate_index += 1) {
        const candidate = scratch.candidates[candidate_index];
        const left: usize = candidate.left;
        const right: usize = candidate.right;
        if (!live(live_mask, left) or !live(live_mask, right)) continue;

        const saved = branch.snapshot();
        const next_mask = pairResultLiveMask(live_mask, candidate);
        const next_sign = sign * pairSign(scratch, live_mask, left, right);
        try pushBranchPairTerm(Tactic, config_ptr, ops, branch, candidate);
        branch_count += try walkAccumulated(Tactic, config_ptr, ops, scratch, branch, next_mask, candidate_index + 1, candidate_count, depth + 1, next_sign, sink);
        branch.restore(saved);
        if (candidate.mandatory_before_base) return branch_count;
    }

    return branch_count;
}

fn walk(
    comptime Tactic: type,
    config_ptr: *const Tactic.Config,
    ops: kernel.Call.MultiOp,
    scratch: anytype,
    live_mask: u128,
    next_candidate_index: usize,
    candidate_count: usize,
    depth: usize,
    sign: i8,
    emit: bool,
    sink: anytype,
) !usize {
    var branch_count: usize = 0;
    const forced_residual = firstForcedResidual(scratch, live_mask);

    if (forced_residual == null and !hasMandatoryCandidate(scratch, live_mask, next_candidate_index, candidate_count)) {
        const residual = residualSlice(scratch, ops.operators.len, live_mask);
        if (try zeroModeSucceeds(Tactic, config_ptr, ops, residual)) {
            if (emit) try emitBranch(Tactic, config_ptr, ops, scratch, depth, sign, residual, sink);
            branch_count += 1;
        }
    }

    if (depth == scratch.pair_stack.len) return branch_count;

    if (forced_residual) |forced| {
        var candidate_link = scratch.first_candidate_by_operator[forced];
        while (candidate_link != no_candidate_index) {
            const candidate_index: usize = candidate_link;
            const candidate = scratch.candidates[candidate_index];
            candidate_link = nextCandidateForOperator(candidate, forced);
            if (candidate_index < next_candidate_index) continue;
            const left: usize = candidate.left;
            const right: usize = candidate.right;
            if (!live(live_mask, left) or !live(live_mask, right)) continue;

            const next_mask = pairResultLiveMask(live_mask, candidate);
            const next_sign = sign * pairSign(scratch, live_mask, left, right);
            if (!emit) {
                branch_count += try walk(Tactic, config_ptr, ops, scratch, next_mask, candidate_index + 1, candidate_count, depth + 1, next_sign, false, sink);
                if (candidate.mandatory_before_base) return branch_count;
                continue;
            }

            scratch.pair_stack[depth] = .{ .left = candidate.left, .right = candidate.right, .term_index = candidate.term_index, .payload = candidate.payload };
            branch_count += try walk(Tactic, config_ptr, ops, scratch, next_mask, candidate_index + 1, candidate_count, depth + 1, next_sign, true, sink);
            if (candidate.mandatory_before_base) return branch_count;
        }
        return branch_count;
    }

    var candidate_index = next_candidate_index;
    while (candidate_index < candidate_count) : (candidate_index += 1) {
        const candidate = scratch.candidates[candidate_index];
        const left: usize = candidate.left;
        const right: usize = candidate.right;
        if (!live(live_mask, left) or !live(live_mask, right)) continue;

        const next_mask = pairResultLiveMask(live_mask, candidate);
        const next_sign = sign * pairSign(scratch, live_mask, left, right);
        if (!emit) {
            branch_count += try walk(Tactic, config_ptr, ops, scratch, next_mask, candidate_index + 1, candidate_count, depth + 1, next_sign, false, sink);
            if (candidate.mandatory_before_base) return branch_count;
            continue;
        }

        scratch.pair_stack[depth] = .{ .left = candidate.left, .right = candidate.right, .term_index = candidate.term_index, .payload = candidate.payload };
        branch_count += try walk(Tactic, config_ptr, ops, scratch, next_mask, candidate_index + 1, candidate_count, depth + 1, next_sign, true, sink);
        if (candidate.mandatory_before_base) return branch_count;
    }

    return branch_count;
}

/// wickCorrelator streams all Wick branches accepted by the tactic base case.
pub fn wickCorrelator(
    comptime Tactic: type,
    config_ptr: *const Tactic.Config,
    ops: kernel.Call.MultiOp,
    sink: anytype,
) !void {
    const max_operator_count = tacticOperatorCount(Tactic);
    var scratch_storage = Scratch(max_operator_count).init();
    const scratch = &scratch_storage;
    if (ops.operators.len > max_operator_count) return error.TooManyWickOperators;
    const candidate_count = try buildCandidates(Tactic, config_ptr, ops, scratch);
    buildParities(Tactic, config_ptr, ops, scratch);
    buildZeroModeSurvivability(Tactic, config_ptr, ops, scratch);
    if (@hasDecl(Tactic, "BranchState") and @hasDecl(Tactic, "pushBranchPairTerm") and @hasDecl(Tactic, "emitAccumulatedBranch")) {
        var branch = if (@hasDecl(Tactic, "initBranchState"))
            try Tactic.initBranchState(config_ptr, ops)
        else
            Tactic.BranchState.init();
        if (pureFullContraction(scratch, ops, candidate_count)) {
            _ = try walkFullAccumulated(Tactic, config_ptr, ops, scratch, &branch, initialLiveMask(max_operator_count, ops.operators.len), 0, 1, sink);
            return;
        }
        _ = try walkAccumulated(Tactic, config_ptr, ops, scratch, &branch, initialLiveMask(max_operator_count, ops.operators.len), 0, candidate_count, 0, 1, sink);
        return;
    }
    _ = try walk(Tactic, config_ptr, ops, scratch, initialLiveMask(max_operator_count, ops.operators.len), 0, candidate_count, 0, 1, true, sink);
}
