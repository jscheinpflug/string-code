const std = @import("std");
const rendering = @import("rendering.zig");
const symmetry = @import("symmetry.zig");

const max_young_rows = 8;
const max_tensor_label_rank = 8;
const max_tensor_young_boxes = 8;
const max_tensor_slots = max_vector_young_boxes;
const max_tensor_raw_diagrams = 128;
const max_tensor_candidates = 128;
const max_tensor_pivots = 32;
const max_tensor_endpoint_projectors = 3;
const max_tensor_word_factors = 8;
const max_tensor_trace_path_steps = max_vector_brauer_candidates;
const max_tensor_trace_removal_branches = max_vector_brauer_candidates;
const max_tensor_endpoint_actions = max_tensor_raw_diagrams * 3;
const max_tensor_endpoint_action_words = max_vector_brauer_candidate_words;
const max_tensor_gram_action_pair_work = 2_000_000;
const max_tensor_term_pair_work = 2_000_000;
const max_tensor_merged_terms = std.math.maxInt(u16);
const max_vector_young_boxes = 8;
const max_vector_brauer_terms = 255;
const max_vector_brauer_atoms = 16;
const max_vector_brauer_edges = max_vector_young_boxes;
const max_vector_brauer_candidates = 32;
const max_vector_brauer_candidate_words = max_vector_brauer_terms;
const max_vector_brauer_gram_entries = max_vector_brauer_candidates * max_vector_brauer_candidates;
const max_young_permutation_terms = 255;

/// TensorFormGammaSpec describes a terminal gamma-form projector expression.
pub const TensorFormGammaSpec = struct {
    operator_id: u32,
    left: rendering.IndexRef,
    right: rendering.IndexRef,
    output: rendering.IndexRef,
    orthogonal_dimension: u16,
    input_form_profile: u128,
    output_form_profile: u128,
    chirality: u8,
};

/// VectorSpinorTracelessSpec describes the rank-one trace-subtraction projector.
pub const VectorSpinorTracelessSpec = struct {
    operator_id: u32,
    vector: rendering.IndexRef,
    spinor: rendering.IndexRef,
    orthogonal_dimension: u16,
    chirality: u8,
};

/// TensorSpinorProjectionSpec describes a tensor-spinor projection lowering request.
pub const TensorSpinorProjectionSpec = struct {
    operator_id: u32,
    left: rendering.IndexRef,
    right: rendering.IndexRef,
    output: rendering.IndexRef,
    orthogonal_dimension: u16,
    left_has_spinor: bool = true,
    right_has_spinor: bool = true,
    output_has_spinor: bool = true,
    right_chirality: u8 = 255,
    input_form_profile: u128 = 0,
    input_form_count: u8 = 0,
    input_tower_power: u16 = 0,
    form_rank: u8,
    form_count: u8 = 1,
    form_mask: u64 = 0,
    form_profile: u128 = 0,
    tower_power: u16,
    chirality: u8,
    duality: rendering.DualityTag = .none,
};

/// TensorFormProjectionSpec describes a tensor-form projection lowering request.
pub const TensorFormProjectionSpec = struct {
    operator_id: u32,
    left: rendering.IndexRef,
    right: rendering.IndexRef,
    output: rendering.IndexRef,
    orthogonal_dimension: u16,
    input_form_profile: u128,
    input_form_mask: u64,
    output_form_profile: u128,
    output_form_count: u8,
    output_form_rank: u8,
    output_duality: rendering.DualityTag = .none,
    right_chirality: u8 = 0,
    chirality: u8,
};

/// StructuralEndpoint describes one local representation endpoint for solver candidate generation.
pub const StructuralEndpoint = struct {
    index: rendering.IndexRef,
    form_profile: u128 = 0,
    form_mask: u64 = 0,
    form_count: u8 = 0,
    form_rank: u8 = 0,
    form_duality: rendering.DualityTag = .none,
    young_row_count: u8 = 0,
    young_rows: [max_young_rows]u8 = [_]u8{0} ** max_young_rows,
    young_box_count: u8 = 0,
    tower_power: u16 = 0,
    chirality: u8 = 0,
    has_spinor: bool = false,
};

/// YoungShape stores one bounded orthogonal vector Young shape.
pub const YoungShape = struct {
    row_count: u8 = 0,
    rows: [max_young_rows]u8 = [_]u8{0} ** max_young_rows,
    box_count: u8 = 0,
};

const OrthogonalTensorKind = enum {
    scalar,
    vector_young,
    exterior_form,
    spinor,
    tensor_spinor,
    mixed_tensor_form,
    unsupported,
};

const OrthogonalTensorDescriptor = struct {
    kind: OrthogonalTensorKind = .unsupported,
    family: symmetry.LieFamily = .b,
    rank: u8 = 0,
    dimension: u16 = 0,
    label_count: u8 = 0,
    labels: [max_tensor_label_rank]i16 = [_]i16{0} ** max_tensor_label_rank,
    young_row_count: u8 = 0,
    young_rows: [max_young_rows]u8 = [_]u8{0} ** max_young_rows,
    young_box_count: u8 = 0,
    column_count: u8 = 0,
    column_heights: [max_young_rows]u8 = [_]u8{0} ** max_young_rows,
    form_rank: u8 = 0,
    form_profile: u128 = 0,
    form_mask: u64 = 0,
    form_duality: rendering.DualityTag = .none,
    has_spinor: bool = false,
    chirality: u8 = 0,
    tower_power: u16 = 0,
};

/// VectorSlotProjectorSpec describes a pure vector tensor projector.
pub const VectorSlotProjectorSpec = struct {
    operator_id: u32,
    dimension: u16,
    left: rendering.IndexRef,
    left_slot_count: u8 = 1,
    left_form_profile: u128 = 0,
    right: rendering.IndexRef,
    right_slot_count: u8 = 1,
    right_form_profile: u128 = 0,
    output: rendering.IndexRef,
    output_form_profile: u128 = 0,
    shape: YoungShape,
};

const TensorPairingSpec = struct {
    operator_id: u32,
    dimension: u16,
    left: rendering.IndexRef,
    left_form_profile: u128 = 0,
    right: rendering.IndexRef,
    right_form_profile: u128 = 0,
    shape: YoungShape,
};

const TensorContractionSpec = struct {
    operator_id: u32,
    dimension: u16,
    left: rendering.IndexRef,
    left_slot_count: u8,
    left_form_profile: u128 = 0,
    right: rendering.IndexRef,
    right_slot_count: u8,
    right_form_profile: u128 = 0,
    output: rendering.IndexRef,
    output_form_profile: u128 = 0,
    shape: YoungShape,
    contraction_count: u8 = 0,
};

const TensorContractionPairing = struct {
    count: u8 = 0,
    left_slots: [max_vector_young_boxes]u8 = [_]u8{0} ** max_vector_young_boxes,
    right_slots: [max_vector_young_boxes]u8 = [_]u8{0} ** max_vector_young_boxes,

    fn append(self: *TensorContractionPairing, left_slot: u8, right_slot: u8) !void {
        if (self.count == max_vector_young_boxes) return error.UnsupportedTensorPrimitiveTermCap;
        self.left_slots[self.count] = left_slot;
        self.right_slots[self.count] = right_slot;
        self.count += 1;
    }

    fn pop(self: *TensorContractionPairing) void {
        self.count -= 1;
    }

    fn containsLeft(self: TensorContractionPairing, left_slot: u8) bool {
        var index: u8 = 0;
        while (index < self.count) : (index += 1) {
            if (self.left_slots[index] == left_slot) return true;
        }
        return false;
    }

    fn containsRight(self: TensorContractionPairing, right_slot: u8) bool {
        var index: u8 = 0;
        while (index < self.count) : (index += 1) {
            if (self.right_slots[index] == right_slot) return true;
        }
        return false;
    }

    fn containsInput(self: TensorContractionPairing, left_slot_count: u8, input_slot: u8) bool {
        var index: u8 = 0;
        while (index < self.count) : (index += 1) {
            if (input_slot == self.left_slots[index]) return true;
            if (input_slot == left_slot_count + self.right_slots[index]) return true;
        }
        return false;
    }
};

const TensorEndpointSide = enum {
    left,
    right,
    output,
};

const ExplicitEndpoint = struct {
    side: TensorEndpointSide,
    block: rendering.IndexRef,
    descriptor: OrthogonalTensorDescriptor,
    vector_slot_count: u8 = 0,
    has_spinor: bool = false,
};

const TensorCompilerChannel = struct {
    operator_id: u32,
    dimension: u16,
    left: ExplicitEndpoint,
    right: ExplicitEndpoint,
    output: ExplicitEndpoint,
};

const TensorOnlyEndpointKind = enum {
    scalar,
    vector_young,
    exterior_form,
    mixed_tensor_form,
    hodge_form,
};

const TensorOnlyEndpointSlot = struct {
    block: rendering.IndexBlockId = 0,
    slot: u8 = 0,
};

const TensorOnlyEndpointLayout = struct {
    slot_count: u8 = 0,
    slots: [max_tensor_slots]TensorOnlyEndpointSlot = [_]TensorOnlyEndpointSlot{.{}} ** max_tensor_slots,
};

const TensorOnlyEndpoint = struct {
    side: TensorEndpointSide,
    block: rendering.IndexRef,
    kind: TensorOnlyEndpointKind,
    slot_count: u8 = 0,
    layout: TensorOnlyEndpointLayout = .{},
    rows: [max_young_rows]u8 = [_]u8{0} ** max_young_rows,
    row_count: u8 = 0,
    column_heights: [max_young_rows]u8 = [_]u8{0} ** max_young_rows,
    column_count: u8 = 0,
    form_profile: u128 = 0,
    form_mask: u64 = 0,
    form_rank: u8 = 0,
    duality: rendering.DualityTag = .none,
};

const TensorOnlyChannel = struct {
    operator_id: u32,
    dimension: u16,
    left: TensorOnlyEndpoint,
    right: TensorOnlyEndpoint,
    output: TensorOnlyEndpoint,
    input_slot_count: u8 = 0,
    output_slot_count: u8 = 0,
};

const TensorOnlyFactorKind = enum {
    left_projector,
    right_projector,
    output_projector,
    raw_brauer_diagram,
    hodge_projector,
};

const TensorOnlyFactor = struct {
    kind: TensorOnlyFactorKind = .raw_brauer_diagram,
    candidate_index: u8 = 0,
};

const TensorOnlyCandidateWord = struct {
    coefficient: Rational = Rational.one(),
    factor_count: u8 = 0,
    factors: [max_tensor_word_factors]TensorOnlyFactor = [_]TensorOnlyFactor{.{}} ** max_tensor_word_factors,

    fn append(self: *TensorOnlyCandidateWord, factor: TensorOnlyFactor) !void {
        if (self.factor_count == max_tensor_word_factors) return error.UnsupportedTensorPrimitiveTermCap;
        self.factors[self.factor_count] = factor;
        self.factor_count += 1;
    }
};

const TensorChannelKind = enum {
    young_output,
    scalar_pairing,
    tensor_contraction,
    compressed_form_bridge,
    spinor_clifford_bridge,
};

const TensorPrimitiveKind = enum {
    vector_young_output,
    vector_young_pairing,
    vector_tensor_contraction,
    structural_projection,
    form_bridge,
    spinor_bridge,
};

const TensorPrimitive = struct {
    kind: TensorPrimitiveKind = .form_bridge,
    candidate_index: u8 = 0,
};

const max_tensor_candidate_primitives = 8;

const TensorCandidateWord = struct {
    coefficient: Rational = Rational.one(),
    primitive_count: u8 = 0,
    primitives: [max_tensor_candidate_primitives]TensorPrimitive = [_]TensorPrimitive{.{}} ** max_tensor_candidate_primitives,

    fn append(self: *TensorCandidateWord, primitive: TensorPrimitive) !void {
        if (self.primitive_count == max_tensor_candidate_primitives) return error.UnsupportedTensorPrimitiveTermCap;
        self.primitives[self.primitive_count] = primitive;
        self.primitive_count += 1;
    }
};

const TensorCandidateBuffer = struct {
    count: u8 = 0,
    words: [max_program_candidates]TensorCandidateWord = [_]TensorCandidateWord{.{}} ** max_program_candidates,

    fn append(self: *TensorCandidateBuffer, word: TensorCandidateWord) !void {
        if (self.count == max_program_candidates) return error.UnsupportedTensorBrauerCandidateCap;
        self.words[self.count] = word;
        self.count += 1;
    }
};

const VectorBrauerAtomKind = enum {
    delta,
    metric,
    hodge_star,
};

const VectorBrauerAtom = struct {
    kind: VectorBrauerAtomKind = .delta,
    upper: rendering.IndexBlockId = 0,
    upper_slot: u8 = 0,
    lower: rendering.IndexBlockId = 0,
    lower_slot: u8 = 0,
    left: rendering.IndexBlockId = 0,
    left_slot: u8 = 0,
    right: rendering.IndexBlockId = 0,
    right_slot: u8 = 0,
    hodge_input: rendering.IndexBlockId = 0,
    hodge_output: rendering.IndexBlockId = 0,
};

const BrauerEdgeKind = enum {
    delta,
    input_trace,
    output_metric,
};

const BrauerEdge = struct {
    kind: BrauerEdgeKind = .delta,
    input_a: u8 = 0,
    input_b: u8 = 0,
    output_a: u8 = 0,
    output_b: u8 = 0,
};

const BrauerWord = struct {
    coefficient: Rational = Rational.zero(),
    edge_count: u8 = 0,
    edges: [max_vector_brauer_edges]BrauerEdge = [_]BrauerEdge{.{}} ** max_vector_brauer_edges,
};

const BrauerCandidate = struct {
    word_count: u8 = 0,
    words: [max_vector_brauer_candidate_words]BrauerWord = [_]BrauerWord{.{}} ** max_vector_brauer_candidate_words,

    fn append(self: *BrauerCandidate, word: BrauerWord) !void {
        if (self.word_count == max_vector_brauer_candidate_words) return error.UnsupportedTensorBrauerCandidateCap;
        self.words[self.word_count] = word;
        self.word_count += 1;
    }
};

const BrauerCandidateBuffer = struct {
    count: u8 = 0,
    candidates: [max_vector_brauer_candidates]BrauerCandidate = [_]BrauerCandidate{.{}} ** max_vector_brauer_candidates,

    fn append(self: *BrauerCandidateBuffer, candidate: BrauerCandidate) !void {
        if (self.count == max_vector_brauer_candidates) return error.UnsupportedTensorBrauerCandidateCap;
        self.candidates[self.count] = candidate;
        self.count += 1;
    }
};

const YoungPermutationTerm = struct {
    coefficient: Rational = Rational.zero(),
    permutation: [max_vector_young_boxes]u8 = [_]u8{0} ** max_vector_young_boxes,
};

const YoungPermutationSum = struct {
    count: u8 = 0,
    terms: [max_young_permutation_terms]YoungPermutationTerm = [_]YoungPermutationTerm{.{}} ** max_young_permutation_terms,
};

const VectorBrauerTerm = struct {
    coefficient: Rational = Rational.zero(),
    atom_count: u8 = 0,
    atoms: [max_vector_brauer_atoms]VectorBrauerAtom = [_]VectorBrauerAtom{.{}} ** max_vector_brauer_atoms,
};

const VectorBrauerProgram = struct {
    candidate_count: u8 = 0,
    pivot_count: u8 = 0,
    term_count: u8 = 0,
    candidates: [max_vector_brauer_candidates]BrauerCandidate = [_]BrauerCandidate{.{}} ** max_vector_brauer_candidates,
    pivots: [max_vector_brauer_candidates]u8 = [_]u8{0} ** max_vector_brauer_candidates,
    inverse_gram: [max_vector_brauer_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_vector_brauer_gram_entries,
    terms: [max_vector_brauer_terms]VectorBrauerTerm = [_]VectorBrauerTerm{.{}} ** max_vector_brauer_terms,
};

const CachedVectorProgramKind = enum {
    projector,
    pairing,
    contraction,
    structural,
};

const CachedVectorProgramKey = struct {
    kind: CachedVectorProgramKind,
    dimension: u16,
    left: rendering.IndexBlockId,
    left_slot_count: u8,
    left_form_profile: u128,
    right: rendering.IndexBlockId,
    right_slot_count: u8,
    right_form_profile: u128,
    output: rendering.IndexBlockId,
    output_form_profile: u128,
    row_count: u8,
    rows: [max_young_rows]u8,
    box_count: u8,
};

const TraceFreeBrauerProjector = struct {
    basis_count: u8 = 0,
    basis: []BrauerCandidate = &.{},
    coefficients: []Rational = &.{},
    paths: []TraceRemovalPath = &.{},

    fn deinit(self: *TraceFreeBrauerProjector) void {
        const allocator = std.heap.page_allocator;
        allocator.free(self.basis);
        allocator.free(self.coefficients);
        allocator.free(self.paths);
        self.* = .{};
    }
};

const TraceRemovalPath = struct {
    trace_count: u8 = 0,
    trace_indices: [max_tensor_trace_path_steps]u8 = [_]u8{0} ** max_tensor_trace_path_steps,
};

const TraceRemovalPathBuffer = struct {
    count: u8 = 0,
    paths: [max_vector_brauer_candidates]TraceRemovalPath = [_]TraceRemovalPath{.{}} ** max_vector_brauer_candidates,

    fn append(self: *TraceRemovalPathBuffer, path: TraceRemovalPath) !void {
        if (self.count == max_vector_brauer_candidates) return error.UnsupportedTensorBrauerCandidateCap;
        self.paths[self.count] = path;
        self.count += 1;
    }
};

const TensorTraceRemovalBranch = struct {
    coefficient: Rational = Rational.zero(),
    trace_count: u8 = 0,
    trace_slot_a: [max_tensor_trace_path_steps]u8 = [_]u8{0} ** max_tensor_trace_path_steps,
    trace_slot_b: [max_tensor_trace_path_steps]u8 = [_]u8{0} ** max_tensor_trace_path_steps,
};

const TensorBrauerDiagram = BrauerWord;

const TensorBrauerDiagramBuffer = struct {
    count: u8 = 0,
    diagrams: [max_tensor_raw_diagrams]TensorBrauerDiagram = [_]TensorBrauerDiagram{.{}} ** max_tensor_raw_diagrams,

    fn append(self: *TensorBrauerDiagramBuffer, diagram: TensorBrauerDiagram) !void {
        if (self.count == max_tensor_raw_diagrams) return error.UnsupportedTensorBrauerCandidateCap;
        self.diagrams[self.count] = diagram;
        self.count += 1;
    }
};

const EndpointProjector = struct {
    is_identity: bool = true,
    diagnostic_trace_free_basis: bool = false,
    operator_count: u8 = 0,
    operators: [max_tensor_word_factors]TensorEndpointOperatorFactor = [_]TensorEndpointOperatorFactor{.{}} ** max_tensor_word_factors,
    trace_free: TraceFreeBrauerProjector = .{},
    trace_branch_count: u8 = 0,
    trace_branches: [max_tensor_trace_removal_branches]TensorTraceRemovalBranch = [_]TensorTraceRemovalBranch{.{}} ** max_tensor_trace_removal_branches,
    hodge_duality: rendering.DualityTag = .none,

    fn deinit(self: *EndpointProjector) void {
        self.trace_free.deinit();
        self.* = .{};
    }
};

const TensorOnlyEndpointProjectorKey = struct {
    kind: TensorOnlyEndpointKind = .scalar,
    slot_count: u8 = 0,
    row_count: u8 = 0,
    rows: [max_young_rows]u8 = [_]u8{0} ** max_young_rows,
    hodge_duality: rendering.DualityTag = .none,
};

const TensorEndpointOperatorKind = enum {
    young_row_symmetrizer,
    young_column_antisymmetrizer,
    scalar_multiplier,
    trace_removal_projector,
    young_trace_free_projector,
    hodge_projector,
};

const TensorEndpointOperatorFactor = struct {
    kind: TensorEndpointOperatorKind = .young_trace_free_projector,
    projector_index: u8 = 0,
    slot_count: u8 = 0,
    slots: [max_tensor_slots]u8 = [_]u8{0} ** max_tensor_slots,
    row_factor_count: u8 = 0,
    column_factor_count: u8 = 0,
    trace_generator_count: u8 = 0,
    young_word_upper_bound: u16 = 0,
    trace_basis_count: u8 = 0,
    trace_branch_first: u8 = 0,
    trace_branch_count: u8 = 0,
    trace_slot_a: u8 = 0,
    trace_slot_b: u8 = 0,
    trace_coefficient: Rational = Rational.zero(),
    scalar_coefficient: Rational = Rational.one(),
};

const TensorOnlyPairTermIndex = struct {
    first_term: u16 = 0,
    term_count: u16 = 0,
};

const TensorEndpointActionKey = struct {
    endpoint_projector_index: u8 = 0,
    side: TensorEndpointSide = .left,
    raw_diagram_index: u8 = 0,
    input_word_count: u8 = 0,
    boundary_signature: u64 = 0,
};

const TensorEndpointHodgeAction = struct {
    side: TensorEndpointSide = .left,
    block: rendering.IndexBlockId = 0,
    duality: rendering.DualityTag = .none,
};

const TensorEndpointActionWord = struct {
    word: BrauerWord = .{},
    hodge_count: u8 = 0,
    hodge_actions: [max_tensor_endpoint_projectors]TensorEndpointHodgeAction = [_]TensorEndpointHodgeAction{.{}} ** max_tensor_endpoint_projectors,
};

const TensorEndpointActionBuffer = struct {
    key: TensorEndpointActionKey = .{},
    word_count: u8 = 0,
    words: []TensorEndpointActionWord = &.{},

    fn deinit(self: *TensorEndpointActionBuffer) void {
        const allocator = std.heap.page_allocator;
        allocator.free(self.words);
        self.* = .{};
    }
};

const TensorEndpointActionBuildBuffer = struct {
    word_count: u8 = 0,
    words: [max_tensor_endpoint_action_words]TensorEndpointActionWord = [_]TensorEndpointActionWord{.{}} ** max_tensor_endpoint_action_words,
};

const TensorOnlyProgram = struct {
    channel: TensorOnlyChannel,
    raw_diagram_count: u8 = 0,
    raw_diagrams: [max_tensor_raw_diagrams]TensorBrauerDiagram = [_]TensorBrauerDiagram{.{}} ** max_tensor_raw_diagrams,
    projector_count: u8 = 0,
    projector_keys: [max_tensor_endpoint_projectors]TensorOnlyEndpointProjectorKey = [_]TensorOnlyEndpointProjectorKey{.{}} ** max_tensor_endpoint_projectors,
    projectors: [max_tensor_endpoint_projectors]EndpointProjector = [_]EndpointProjector{.{}} ** max_tensor_endpoint_projectors,
    left_projector_index: u8 = 0,
    right_projector_index: u8 = 0,
    output_projector_index: u8 = 0,
    endpoint_action_count: u16 = 0,
    endpoint_actions: [max_tensor_endpoint_actions]TensorEndpointActionBuffer = [_]TensorEndpointActionBuffer{.{}} ** max_tensor_endpoint_actions,
    projected_raw_action_indices: [max_tensor_raw_diagrams]u16 = [_]u16{0} ** max_tensor_raw_diagrams,
    candidate_count: u8 = 0,
    candidates: [max_tensor_candidates]TensorOnlyCandidateWord = [_]TensorOnlyCandidateWord{.{}} ** max_tensor_candidates,
    pivot_count: u8 = 0,
    pivots: [max_tensor_pivots]u8 = [_]u8{0} ** max_tensor_pivots,
    inverse_gram: [max_tensor_pivots * max_tensor_pivots]Rational = [_]Rational{Rational.zero()} ** (max_tensor_pivots * max_tensor_pivots),
    pair_term_indices: [max_tensor_pivots * max_tensor_pivots]TensorOnlyPairTermIndex = [_]TensorOnlyPairTermIndex{.{}} ** (max_tensor_pivots * max_tensor_pivots),
    active_pair_term_count: u16 = 0,
    active_pair_term_indices: [max_tensor_pivots * max_tensor_pivots]u16 = [_]u16{0} ** (max_tensor_pivots * max_tensor_pivots),
    merged_terms: []VectorBrauerTerm = &.{},
    term_count: u16 = 0,

    fn deinit(self: *TensorOnlyProgram) void {
        const allocator = std.heap.page_allocator;
        var projector_index: u8 = 0;
        while (projector_index < self.projector_count) : (projector_index += 1) {
            self.projectors[projector_index].deinit();
        }
        var action_index: u16 = 0;
        while (action_index < self.endpoint_action_count) : (action_index += 1) {
            self.endpoint_actions[action_index].deinit();
        }
        allocator.free(self.merged_terms);
        self.* = .{ .channel = self.channel };
    }
};

const VectorBrauerProgramTerm = struct {
    left_candidate: u8,
    right_candidate: u8,
    coefficient: Rational,
};

const BrauerEquationKey = struct {
    trace_index: u8 = 0,
    word: BrauerWord = .{},
};

const BrauerEquationSystem = struct {
    row_count: u16 = 0,
    column_count: u8 = 0,
    keys: [max_vector_brauer_gram_entries]BrauerEquationKey = [_]BrauerEquationKey{.{}} ** max_vector_brauer_gram_entries,
    entries: [max_vector_brauer_gram_entries * (max_vector_brauer_candidates + 1)]Rational = [_]Rational{Rational.zero()} ** (max_vector_brauer_gram_entries * (max_vector_brauer_candidates + 1)),
};

const VectorBrauerPivotSelection = struct {
    count: u8 = 0,
    pivots: [max_vector_brauer_candidates]u8 = [_]u8{0} ** max_vector_brauer_candidates,
};

/// StructuralProjectorSpec describes a representation-channel projector independently of formula family names.
pub const StructuralProjectorSpec = struct {
    operator_id: u32,
    orthogonal_dimension: u16,
    left: StructuralEndpoint,
    right: StructuralEndpoint,
    output: StructuralEndpoint,
};

/// TensorFormProjectionTransition names the profile-level projector class.
pub const TensorFormProjectionTransition = enum {
    gamma_delta,
    rank_split,
    middle_dual,
    unsupported,
};

/// StructuralProjectorKeySummary describes one structural audit key without operator or index ids.
pub const StructuralProjectorKeySummary = struct {
    dimension: u16 = 0,
    source_form_profile: u128 = 0,
    target_form_profile: u128 = 0,
    source_tower_power: u16 = 0,
    target_tower_power: u16 = 0,
    source_has_spinor: bool = false,
    right_has_spinor: bool = false,
    target_has_spinor: bool = false,
    source_chirality: u8 = 0,
    right_chirality: u8 = 0,
    target_chirality: u8 = 0,
    duality: rendering.DualityTag = .none,
};

const max_structural_audit_keys = 64;
const max_structural_unsupported_groups = 4;

/// StructuralProjectorCoverageAudit counts profile classes and solver coverage.
pub const StructuralProjectorCoverageAudit = struct {
    tensor_spinor_projection_count: u64 = 0,
    tensor_spinor_structural_count: u64 = 0,
    tensor_form_projection_count: u64 = 0,
    tensor_form_structural_count: u64 = 0,
    preserve_count: u64 = 0,
    add_rank_count: u64 = 0,
    shift_all_up_count: u64 = 0,
    move_rank_up_count: u64 = 0,
    split_rank_count: u64 = 0,
    remove_rank_count: u64 = 0,
    unsupported_transform_count: u64 = 0,
    structural_projection_count: u64 = 0,
    structural_projection_solved_count: u64 = 0,
    structural_projection_unsupported_count: u64 = 0,
    distinct_structural_key_count: u64 = 0,
    distinct_structural_solved_key_count: u64 = 0,
    distinct_structural_unsupported_key_count: u64 = 0,
    structural_key_overflow_count: u64 = 0,
    structural_key_hashes: [max_structural_audit_keys]u64 = [_]u64{0} ** max_structural_audit_keys,
    structural_key_solved: [max_structural_audit_keys]bool = [_]bool{false} ** max_structural_audit_keys,
    structural_key_occurrences: [max_structural_audit_keys]u64 = [_]u64{0} ** max_structural_audit_keys,
    largest_unsupported_key_hashes: [max_structural_unsupported_groups]u64 = [_]u64{0} ** max_structural_unsupported_groups,
    largest_unsupported_key_counts: [max_structural_unsupported_groups]u64 = [_]u64{0} ** max_structural_unsupported_groups,
    largest_unsupported_key_summaries: [max_structural_unsupported_groups]StructuralProjectorKeySummary = [_]StructuralProjectorKeySummary{.{}} ** max_structural_unsupported_groups,

    /// recordTensorSpinorProjection classifies one tensor-spinor local channel.
    pub fn recordTensorSpinorProjection(self: *StructuralProjectorCoverageAudit, spec: TensorSpinorProjectionSpec) void {
        self.tensor_spinor_projection_count += 1;
        self.recordProfileTransform(classifyProfileTransform(spec.input_form_profile, spec.form_profile));
        if (self.recordStructuralProjection(structuralProjectorSpecFromTensorSpinor(spec))) {
            self.tensor_spinor_structural_count += 1;
        }
    }

    /// recordTensorSpinorAtom classifies one rendered compact tensor-spinor atom.
    pub fn recordTensorSpinorAtom(self: *StructuralProjectorCoverageAudit, atom: rendering.TensorSpinorProjection) void {
        self.recordTensorSpinorProjection(.{
            .operator_id = atom.operator_id,
            .left = atom.left,
            .right = atom.right,
            .output = atom.output,
            .orthogonal_dimension = atom.orthogonal_dimension,
            .input_form_profile = atom.input_form_profile,
            .input_form_count = atom.input_form_count,
            .form_rank = atom.form_rank,
            .form_count = atom.form_count,
            .form_mask = atom.form_mask,
            .form_profile = atom.form_profile,
            .tower_power = atom.tower_power,
            .chirality = atom.chirality,
            .duality = atom.duality,
        });
    }

    /// recordTensorFormProjection classifies one tensor-form local channel.
    pub fn recordTensorFormProjection(self: *StructuralProjectorCoverageAudit, spec: TensorFormProjectionSpec) void {
        self.tensor_form_projection_count += 1;
        self.recordProfileTransform(classifyProfileTransform(spec.input_form_profile, spec.output_form_profile));
        if (self.recordStructuralProjection(structuralProjectorSpecFromTensorForm(spec))) {
            self.tensor_form_structural_count += 1;
        }
    }

    /// recordTensorFormAtom classifies one rendered compact tensor-form atom.
    pub fn recordTensorFormAtom(self: *StructuralProjectorCoverageAudit, atom: rendering.TensorFormProjection, chirality: u8) void {
        self.recordTensorFormProjection(.{
            .operator_id = atom.operator_id,
            .left = atom.left,
            .right = atom.right,
            .output = atom.output,
            .orthogonal_dimension = atom.orthogonal_dimension,
            .input_form_profile = formProfileFromMask(atom.input_form_mask),
            .input_form_mask = atom.input_form_mask,
            .output_form_profile = atom.output_form_profile,
            .output_form_count = atom.output_form_count,
            .output_form_rank = atom.output_form_rank,
            .output_duality = atom.output_duality,
            .right_chirality = atom.right_chirality,
            .chirality = chirality,
        });
    }

    fn recordProfileTransform(self: *StructuralProjectorCoverageAudit, transform: ProfileTransform) void {
        switch (transform.kind) {
            .preserve => self.preserve_count += 1,
            .add_rank => self.add_rank_count += 1,
            .shift_all_up => self.shift_all_up_count += 1,
            .move_rank_up => self.move_rank_up_count += 1,
            .split_rank => self.split_rank_count += 1,
            .remove_rank => self.remove_rank_count += 1,
            .unsupported => self.unsupported_transform_count += 1,
        }
    }

    fn recordStructuralProjection(self: *StructuralProjectorCoverageAudit, spec: StructuralProjectorSpec) bool {
        self.structural_projection_count += 1;
        const key = structuralProgramKey(spec);
        const key_hash = structuralProgramKeyHash(key);
        var slot_index: usize = 0;
        while (slot_index < max_structural_audit_keys) : (slot_index += 1) {
            if (self.structural_key_hashes[slot_index] != key_hash) continue;
            const solved = self.structural_key_solved[slot_index];
            self.structural_key_occurrences[slot_index] += 1;
            if (!solved) self.recordUnsupportedStructuralKeyGroup(key_hash, self.structural_key_occurrences[slot_index], key);
            self.recordStructuralProjectionStatus(solved);
            return solved;
        }

        const solved = structuralProjectorTermCount(spec) != 0;
        self.recordStructuralProjectionStatus(solved);
        self.distinct_structural_key_count += 1;
        if (solved) {
            self.distinct_structural_solved_key_count += 1;
        } else {
            self.distinct_structural_unsupported_key_count += 1;
        }

        slot_index = 0;
        while (slot_index < max_structural_audit_keys) : (slot_index += 1) {
            if (self.structural_key_hashes[slot_index] != 0) continue;
            self.structural_key_hashes[slot_index] = key_hash;
            self.structural_key_solved[slot_index] = solved;
            self.structural_key_occurrences[slot_index] = 1;
            if (!solved) self.recordUnsupportedStructuralKeyGroup(key_hash, 1, key);
            return solved;
        }
        self.structural_key_overflow_count += 1;
        return solved;
    }

    fn recordStructuralProjectionStatus(self: *StructuralProjectorCoverageAudit, solved: bool) void {
        if (solved) {
            self.structural_projection_solved_count += 1;
        } else {
            self.structural_projection_unsupported_count += 1;
        }
    }

    fn recordUnsupportedStructuralKeyGroup(self: *StructuralProjectorCoverageAudit, key_hash: u64, count: u64, key: StructuralProgramKey) void {
        var group_index: usize = 0;
        while (group_index < max_structural_unsupported_groups) : (group_index += 1) {
            if (self.largest_unsupported_key_hashes[group_index] != key_hash) continue;
            self.largest_unsupported_key_counts[group_index] = count;
            self.sortUnsupportedStructuralKeyGroups();
            return;
        }

        group_index = 0;
        while (group_index < max_structural_unsupported_groups) : (group_index += 1) {
            if (self.largest_unsupported_key_hashes[group_index] != 0) continue;
            self.largest_unsupported_key_hashes[group_index] = key_hash;
            self.largest_unsupported_key_counts[group_index] = count;
            self.largest_unsupported_key_summaries[group_index] = structuralProjectorKeySummary(key);
            self.sortUnsupportedStructuralKeyGroups();
            return;
        }

        if (count <= self.largest_unsupported_key_counts[max_structural_unsupported_groups - 1]) return;
        self.largest_unsupported_key_hashes[max_structural_unsupported_groups - 1] = key_hash;
        self.largest_unsupported_key_counts[max_structural_unsupported_groups - 1] = count;
        self.largest_unsupported_key_summaries[max_structural_unsupported_groups - 1] = structuralProjectorKeySummary(key);
        self.sortUnsupportedStructuralKeyGroups();
    }

    fn sortUnsupportedStructuralKeyGroups(self: *StructuralProjectorCoverageAudit) void {
        var outer: usize = 0;
        while (outer < max_structural_unsupported_groups) : (outer += 1) {
            var inner = outer + 1;
            while (inner < max_structural_unsupported_groups) : (inner += 1) {
                if (self.largest_unsupported_key_counts[inner] <= self.largest_unsupported_key_counts[outer]) continue;
                const hash = self.largest_unsupported_key_hashes[outer];
                const count = self.largest_unsupported_key_counts[outer];
                const summary = self.largest_unsupported_key_summaries[outer];
                self.largest_unsupported_key_hashes[outer] = self.largest_unsupported_key_hashes[inner];
                self.largest_unsupported_key_counts[outer] = self.largest_unsupported_key_counts[inner];
                self.largest_unsupported_key_summaries[outer] = self.largest_unsupported_key_summaries[inner];
                self.largest_unsupported_key_hashes[inner] = hash;
                self.largest_unsupported_key_counts[inner] = count;
                self.largest_unsupported_key_summaries[inner] = summary;
            }
        }
    }
};

const TensorSpinorProjectionTransition = enum {
    spinor_tower_contract,
    unsupported,
};

const ProfileTransformKind = enum {
    preserve,
    add_rank,
    shift_all_up,
    move_rank_up,
    split_rank,
    remove_rank,
    unsupported,
};

const ProfileTransform = struct {
    kind: ProfileTransformKind,
    rank: u8 = 0,
    source_rank: u8 = 0,
    target_rank: u8 = 0,
    lower_rank: u8 = 0,
    upper_rank: u8 = 0,
    carried_profile: u128 = 0,
};

const StructuralSearchState = struct {
    form_profile: u128 = 0,
    tower_power: u16 = 0,
    chirality: u8 = 0,
    has_spinor: bool = false,
};

const StructuralPrimitiveEffectKind = enum {
    spinor_tower_contract,
    spinor_tower_contract_adjoint,
    form_spinor_contract_adjoint,
    gamma_insert,
    gamma_wedge_shift,
    gamma_rank_split,
    hodge_project,
};

const StructuralPrimitiveEffect = struct {
    kind: StructuralPrimitiveEffectKind,
    next: StructuralSearchState = .{},
    signature: PrimitiveSignature = .{},
};

const max_structural_generated_effects = 16;
const max_structural_search_depth = max_program_primitives;

const StructuralPrimitiveEffectBuffer = struct {
    count: u8 = 0,
    slots: [max_structural_generated_effects]StructuralPrimitiveEffect = [_]StructuralPrimitiveEffect{.{ .kind = .spinor_tower_contract }} ** max_structural_generated_effects,

    fn append(self: *StructuralPrimitiveEffectBuffer, effect: StructuralPrimitiveEffect) !void {
        if (self.count == max_structural_generated_effects) return error.ProjectorProgramTooLarge;
        self.slots[self.count] = effect;
        self.count += 1;
    }
};

const max_program_primitives = 6;
const max_program_candidates = 128;
const max_program_pivots = 32;
const max_program_candidate_gram_entries = max_program_candidates * max_program_candidates;
const max_program_gram_entries = max_program_pivots * max_program_pivots;

const ProjectorPrimitiveKind = enum {
    form_delta,
    gamma_insert,
    gamma_action,
    gamma_wedge_shift,
    gamma_trace,
    gamma_rank_split,
    hodge_project,
    spinor_tower_contract,
    spinor_tower_contract_adjoint,
    vector_spinor_identity,
};

const ExteriorGammaAction = struct {
    dimension: u8 = 0,
    input_rank: u8 = 0,
    gamma_rank: u8 = 0,
    contraction_count: u8 = 0,
    output_rank: u8 = 0,
    chirality_parity: u1 = 0,
    duality: rendering.DualityTag = .none,
};

const PrimitiveSignature = struct {
    kind: ProjectorPrimitiveKind = .form_delta,
    input_block: rendering.IndexRef = 0,
    output_block: rendering.IndexRef = 0,
    auxiliary_block: rendering.IndexRef = 0,
    action: ExteriorGammaAction = .{},
    tower_input_power: u8 = 0,
    tower_output_power: u8 = 0,
    tower_form_rank: u8 = 0,
    normalization_tag: u8 = 0,
};

const ProjectorPrimitive = struct {
    kind: ProjectorPrimitiveKind,
    input_block: rendering.IndexBlockId = 0,
    output_block: rendering.IndexBlockId = 0,
    auxiliary_block: rendering.IndexBlockId = 0,
    rank: u8 = 0,
    output_rank: u8 = 0,
    auxiliary_rank: u8 = 0,
    action_gamma_rank: u8 = 0,
    action_contraction_count: u8 = 0,
    orthogonal_dimension: u16 = 0,
    chirality: u8 = 0,
    duality: rendering.DualityTag = .none,
};

const ProjectorCandidateWord = struct {
    count: u8 = 0,
    slots: [max_program_primitives]ProjectorPrimitive = [_]ProjectorPrimitive{.{ .kind = .form_delta }} ** max_program_primitives,

    fn append(self: *ProjectorCandidateWord, slot: ProjectorPrimitive) !void {
        if (self.count == max_program_primitives) return error.ProjectorWordTooLarge;
        self.slots[self.count] = slot;
        self.count += 1;
    }
};

const ProjectorCandidateBuffer = struct {
    count: u8 = 0,
    words: [max_program_candidates]ProjectorCandidateWord = [_]ProjectorCandidateWord{.{}} ** max_program_candidates,

    fn append(self: *ProjectorCandidateBuffer, word: ProjectorCandidateWord) !void {
        if (self.count == max_program_candidates) return error.UnsupportedTensorBrauerCandidateCap;
        self.words[self.count] = word;
        self.count += 1;
    }
};

const ProjectorProgram = struct {
    candidate_count: u8 = 0,
    pivot_count: u8 = 0,
    candidates: [max_program_candidates]ProjectorCandidateWord = [_]ProjectorCandidateWord{.{}} ** max_program_candidates,
    pivots: [max_program_pivots]u8 = [_]u8{0} ** max_program_pivots,
    inverse_gram: [max_program_gram_entries]Rational = [_]Rational{.{ .numerator = 0, .denominator = 1 }} ** max_program_gram_entries,
};

const TensorChannelProgram = struct {
    kind: CachedVectorProgramKind = .projector,
    dimension: u16 = 0,
    rank: u8 = 0,
    candidate_count: u8 = 0,
    pivot_count: u8 = 0,
    term_count: u16 = 0,
    pivots: [max_program_pivots]u8 = [_]u8{0} ** max_program_pivots,
    inverse_gram: [max_program_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_program_gram_entries,
    words: [max_program_candidates]TensorCandidateWord = [_]TensorCandidateWord{.{}} ** max_program_candidates,
    vector_program: VectorBrauerProgram = .{},
    vector_spec: VectorSlotProjectorSpec = .{
        .operator_id = 0,
        .dimension = 0,
        .left = 0,
        .right = 0,
        .output = 0,
        .shape = .{},
    },
    structural_spec: StructuralProjectorSpec = .{
        .operator_id = 0,
        .orthogonal_dimension = 0,
        .left = .{ .index = 0 },
        .right = .{ .index = 0 },
        .output = .{ .index = 0 },
    },
    structural_candidates: [max_program_candidates]ProjectorCandidateWord = [_]ProjectorCandidateWord{.{}} ** max_program_candidates,
};

const CachedVectorProgramEntry = struct {
    key: CachedVectorProgramKey,
    program: TensorChannelProgram,
};

const ProjectorCandidateGram = struct {
    context: ?*const anyopaque = null,
    inner_product: *const fn (?*const anyopaque, ProjectorCandidateWord, ProjectorCandidateWord) anyerror!Rational,
};

const ProjectorChannel = union(enum) {
    structural_projection: StructuralProjectorSpec,
    tensor_form_projection: TensorFormProjectionSpec,
    tensor_spinor_projection: TensorSpinorProjectionSpec,
    vector_spinor_traceless: VectorSpinorTracelessSpec,
};

const ProjectorBackend = struct {
    context: ?*const anyopaque = null,
    enumerate_candidates: *const fn (?*const anyopaque, ProjectorChannel, *ProjectorCandidateBuffer) anyerror!void,
    inner_product: *const fn (?*const anyopaque, ProjectorChannel, ProjectorCandidateWord, ProjectorCandidateWord) anyerror!Rational,
};

const ProjectorChannelGramContext = struct {
    channel: ProjectorChannel,
    backend: ProjectorBackend,
};

const ProjectorProgramTerm = struct {
    left_candidate: u8,
    right_candidate: u8,
    coefficient: Rational,
};

const StructuralProjectorProgramCacheEntry = struct {
    key: StructuralProgramKey,
    program: ProjectorProgram,
};

const StructuralTensorProgramCacheEntry = struct {
    key: StructuralProgramKey,
    program: TensorChannelProgram,
};

const TensorOnlyProgramCacheEntry = struct {
    key: StructuralProgramKey,
    program: TensorOnlyProgram,
};

/// StructuralProjectorProgramCache reuses exact Gram programs for orthogonal structural projectors.
pub const StructuralProjectorProgramCache = struct {
    allocator: std.mem.Allocator,
    entries: std.ArrayList(StructuralProjectorProgramCacheEntry) = .empty,
    index_by_hash: std.AutoHashMap(u64, u32),
    vector_entries: std.ArrayList(CachedVectorProgramEntry) = .empty,
    vector_index_by_hash: std.AutoHashMap(u64, u32),
    tensor_entries: std.ArrayList(StructuralTensorProgramCacheEntry) = .empty,
    tensor_index_by_hash: std.AutoHashMap(u64, u32),
    tensor_only_entries: std.ArrayList(TensorOnlyProgramCacheEntry) = .empty,
    tensor_only_index_by_hash: std.AutoHashMap(u64, u32),
    hits: u64 = 0,
    misses: u64 = 0,

    /// init constructs an empty structural projector-program cache.
    pub fn init(allocator: std.mem.Allocator) StructuralProjectorProgramCache {
        return .{
            .allocator = allocator,
            .index_by_hash = std.AutoHashMap(u64, u32).init(allocator),
            .vector_index_by_hash = std.AutoHashMap(u64, u32).init(allocator),
            .tensor_index_by_hash = std.AutoHashMap(u64, u32).init(allocator),
            .tensor_only_index_by_hash = std.AutoHashMap(u64, u32).init(allocator),
        };
    }

    /// deinit releases cached program storage.
    pub fn deinit(self: *StructuralProjectorProgramCache) void {
        for (self.tensor_only_entries.items) |*entry| {
            entry.program.deinit();
        }
        self.tensor_only_index_by_hash.deinit();
        self.tensor_only_entries.deinit(self.allocator);
        self.tensor_index_by_hash.deinit();
        self.tensor_entries.deinit(self.allocator);
        self.vector_index_by_hash.deinit();
        self.vector_entries.deinit(self.allocator);
        self.index_by_hash.deinit();
        self.entries.deinit(self.allocator);
        self.* = StructuralProjectorProgramCache.init(self.allocator);
    }

    /// termCount returns the streamed term count for a structural projector.
    pub fn termCount(self: *StructuralProjectorProgramCache, spec: StructuralProjectorSpec) !u16 {
        if (try tensorCompilerChannelFromStructuralOrNull(spec)) |channel| {
            if (tensorChannelUsesDirectStructuralProgram(channel)) {
                return projectorProgramTermCount(self.programFor(spec) catch |err| switch (err) {
                    error.UnsupportedStructuralProjectorTerm, error.ProjectorProgramTooLarge => return 0,
                    else => return err,
                });
            }
            const count: ?u16 = self.tensorChannelTermCount(channel) catch |err| switch (err) {
                error.UnsupportedTensorBridge => if (tensorChannelStructuralFallbackAllowed(channel)) null else return err,
                else => return err,
            };
            if (count) |value| {
                if (value != 0 or !tensorChannelStructuralFallbackAllowed(channel)) return value;
            }
            if (!tensorChannelStructuralFallbackAllowed(channel)) return 0;
        }
        return projectorProgramTermCount(self.programFor(spec) catch |err| switch (err) {
            error.UnsupportedStructuralProjectorTerm, error.ProjectorProgramTooLarge => return 0,
            else => return err,
        });
    }

    /// appendTerm emits one cached structural projector program term.
    pub fn appendTerm(self: *StructuralProjectorProgramCache, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: StructuralProjectorSpec, term_index: u16) !rendering.RationalId {
        if (try tensorCompilerChannelFromStructuralOrNull(spec)) |channel| {
            if (tensorChannelUsesDirectStructuralProgram(channel)) {
                return appendStructuralProjectorProgramTerm(self.allocator, atoms, spec, try self.programFor(spec), term_index);
            }
            const coefficient: ?rendering.RationalId = self.appendTensorChannelTerm(atoms, channel, term_index) catch |err| switch (err) {
                error.UnsupportedTensorBridge => if (tensorChannelStructuralFallbackAllowed(channel)) null else return err,
                else => return err,
            };
            if (coefficient) |value| return value;
            if (!tensorChannelStructuralFallbackAllowed(channel)) return error.UnsupportedTensorBridge;
        }
        return appendStructuralProjectorProgramTerm(self.allocator, atoms, spec, try self.programFor(spec), term_index);
    }

    /// tensorFormTermCount returns the streamed term count for a tensor-form projection.
    pub fn tensorFormTermCount(self: *StructuralProjectorProgramCache, spec: TensorFormProjectionSpec) !u16 {
        return switch (tensorFormProjectionTransition(spec)) {
            .gamma_delta, .rank_split, .middle_dual => self.termCount(structuralProjectorSpecFromTensorForm(spec)) catch |err| switch (err) {
                error.UnsupportedTensorFormProjectionTerm, error.UnsupportedStructuralProjectorTerm, error.ProjectorProgramTooLarge => return 0,
                else => return err,
            },
            .unsupported => 0,
        };
    }

    /// appendTensorFormTerm emits one cached tensor-form projection term.
    pub fn appendTensorFormTerm(self: *StructuralProjectorProgramCache, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorFormProjectionSpec, term_index: u16) !rendering.RationalId {
        return switch (tensorFormProjectionTransition(spec)) {
            .gamma_delta, .rank_split, .middle_dual => self.appendTerm(atoms, structuralProjectorSpecFromTensorForm(spec), term_index),
            .unsupported => error.UnsupportedTensorFormProjectionTerm,
        };
    }

    /// appendTensorFormExpression emits a tensor-form projection expression for non-expanded rendering.
    pub fn appendTensorFormExpression(self: *StructuralProjectorProgramCache, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorFormProjectionSpec) !bool {
        if (try self.tensorFormTermCount(spec) == 1) {
            _ = try self.appendTensorFormTerm(atoms, spec, 0);
            return true;
        }
        try appendCompactTensorFormProjection(self.allocator, atoms, spec);
        return false;
    }

    /// tensorSpinorTermCount returns the streamed term count for a tensor-spinor projection.
    pub fn tensorSpinorTermCount(self: *StructuralProjectorProgramCache, spec: TensorSpinorProjectionSpec) !u16 {
        return self.termCount(structuralProjectorSpecFromTensorSpinor(spec)) catch |err| switch (err) {
            error.UnsupportedStructuralProjectorTerm, error.UnsupportedTensorSpinorProjectionTerm, error.ProjectorProgramTooLarge => return 0,
            else => return err,
        };
    }

    /// appendTensorSpinorTerm emits one cached tensor-spinor projection term.
    pub fn appendTensorSpinorTerm(self: *StructuralProjectorProgramCache, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorSpinorProjectionSpec, term_index: u16) !rendering.RationalId {
        return self.appendTerm(atoms, structuralProjectorSpecFromTensorSpinor(spec), term_index);
    }

    /// appendTensorSpinorExpression emits a tensor-spinor projection expression for non-expanded rendering.
    pub fn appendTensorSpinorExpression(self: *StructuralProjectorProgramCache, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorSpinorProjectionSpec) !bool {
        if (try self.tensorSpinorTermCount(spec) == 1) {
            _ = try self.appendTensorSpinorTerm(atoms, spec, 0);
            return true;
        }
        try appendCompactTensorSpinorProjection(self.allocator, atoms, spec);
        return false;
    }

    /// entryCount returns the number of compiled structural programs.
    pub fn entryCount(self: StructuralProjectorProgramCache) usize {
        return self.entries.items.len;
    }

    fn programFor(self: *StructuralProjectorProgramCache, spec: StructuralProjectorSpec) !ProjectorProgram {
        const key = structuralProgramKey(spec);
        const key_hash = structuralProgramKeyHash(key);
        if (self.index_by_hash.get(key_hash)) |entry_index| {
            if (entry_index < self.entries.items.len) {
                const entry = self.entries.items[entry_index];
                if (structuralProgramKeyEql(entry.key, key)) {
                    self.hits += 1;
                    return entry.program;
                }
            }
        }
        for (self.entries.items) |entry| {
            if (structuralProgramKeyEql(entry.key, key)) {
                self.hits += 1;
                return entry.program;
            }
        }
        self.misses += 1;
        const program = try compileStructuralProjectorProgram(spec);
        const entry_index: u32 = @intCast(self.entries.items.len);
        try self.entries.append(self.allocator, .{ .key = key, .program = program });
        if (!self.index_by_hash.contains(key_hash)) try self.index_by_hash.put(key_hash, entry_index);
        return program;
    }

    fn tensorProgramFor(self: *StructuralProjectorProgramCache, kind: CachedVectorProgramKind, spec: VectorSlotProjectorSpec) !?TensorChannelProgram {
        const key = cachedVectorProgramKey(kind, spec);
        const key_hash = cachedVectorProgramKeyHash(key);
        if (self.vector_index_by_hash.get(key_hash)) |entry_index| {
            if (entry_index < self.vector_entries.items.len) {
                const entry = self.vector_entries.items[entry_index];
                if (cachedVectorProgramKeyEql(entry.key, key)) {
                    self.hits += 1;
                    return entry.program;
                }
            }
        }
        for (self.vector_entries.items) |entry| {
            if (cachedVectorProgramKeyEql(entry.key, key)) {
                self.hits += 1;
                return entry.program;
            }
        }
        const program = switch (kind) {
            .projector, .pairing => compileVectorBackedTensorChannelProgram(kind, spec),
            .contraction => compileVectorBackedTensorContractionProgram(tensorContractionSpecFromVectorSpec(spec)),
            .structural => error.UnsupportedTensorBridge,
        } catch |err| switch (err) {
            error.UnsupportedTensorPrimitiveTermCap => return null,
            else => return err,
        };
        self.misses += 1;
        const entry_index: u32 = @intCast(self.vector_entries.items.len);
        try self.vector_entries.append(self.allocator, .{ .key = key, .program = program });
        if (!self.vector_index_by_hash.contains(key_hash)) try self.vector_index_by_hash.put(key_hash, entry_index);
        return program;
    }

    fn tensorChannelTermCount(self: *StructuralProjectorProgramCache, channel: TensorCompilerChannel) !?u16 {
        if (try self.tensorOnlyProgramFor(channel)) |program| return program.term_count;

        return switch (tensorChannelKind(channel) catch |err| switch (err) {
            error.UnsupportedTensorBridge => return null,
        }) {
            .young_output => blk: {
                const vector_spec = vectorSlotProjectorSpecFromChannel(channel).?;
                if (try self.tensorProgramFor(.projector, vector_spec)) |program| break :blk program.term_count;
                break :blk vectorSlotProjectorTermCount(vector_spec);
            },
            .scalar_pairing => blk: {
                const pairing_spec = tensorPairingSpecFromChannel(channel).?;
                const vector_spec = vectorProjectorSpecForPairing(pairing_spec);
                if (try self.tensorProgramFor(.pairing, vector_spec)) |program| break :blk program.term_count;
                break :blk tensorPairingTermCount(pairing_spec);
            },
            .tensor_contraction => blk: {
                const vector_spec = vectorProjectorSpecForContraction(tensorContractionSpecFromChannel(channel).?);
                if (try self.tensorProgramFor(.contraction, vector_spec)) |program| break :blk program.term_count;
                break :blk @as(u16, 0);
            },
            .compressed_form_bridge => return error.UnsupportedTensorBridge,
            .spinor_clifford_bridge => blk: {
                if (try self.structuralTensorProgramFor(channel)) |program| break :blk program.term_count;
                break :blk @as(u16, 0);
            },
        };
    }

    fn appendTensorChannelTerm(self: *StructuralProjectorProgramCache, atoms: *std.ArrayList(rendering.SymbolicAtom), channel: TensorCompilerChannel, term_index: u16) !?rendering.RationalId {
        if (try self.tensorOnlyProgramFor(channel)) |program| {
            return try appendTensorOnlyProgramTerm(self.allocator, atoms, program, term_index);
        }

        return switch (tensorChannelKind(channel) catch |err| switch (err) {
            error.UnsupportedTensorBridge => return null,
        }) {
            .young_output => blk: {
                const vector_spec = vectorSlotProjectorSpecFromChannel(channel).?;
                if (try self.tensorProgramFor(.projector, vector_spec)) |program| break :blk try appendTensorChannelProgramTerm(self.allocator, atoms, program, term_index);
                break :blk try appendVectorSlotProjectorTerm(self.allocator, atoms, vector_spec, term_index);
            },
            .scalar_pairing => blk: {
                const pairing_spec = tensorPairingSpecFromChannel(channel).?;
                const vector_spec = vectorProjectorSpecForPairing(pairing_spec);
                if (try self.tensorProgramFor(.pairing, vector_spec)) |program| break :blk try appendTensorChannelProgramTerm(self.allocator, atoms, program, term_index);
                break :blk try appendTensorPairingTerm(self.allocator, atoms, pairing_spec, term_index);
            },
            .tensor_contraction => blk: {
                const vector_spec = vectorProjectorSpecForContraction(tensorContractionSpecFromChannel(channel).?);
                if (try self.tensorProgramFor(.contraction, vector_spec)) |program| break :blk try appendTensorChannelProgramTerm(self.allocator, atoms, program, term_index);
                break :blk null;
            },
            .compressed_form_bridge => return error.UnsupportedTensorBridge,
            .spinor_clifford_bridge => blk: {
                if (try self.structuralTensorProgramFor(channel)) |program| break :blk try appendTensorChannelProgramTerm(self.allocator, atoms, program, term_index);
                break :blk null;
            },
        };
    }

    fn tensorOnlyProgramFor(self: *StructuralProjectorProgramCache, channel: TensorCompilerChannel) !?*const TensorOnlyProgram {
        const tensor_channel = liveTensorOnlyChannelFromCompilerChannel(channel) catch |err| switch (err) {
            error.UnsupportedTensorBridge => return null,
            else => return err,
        };
        const spec = structuralProjectorSpecFromTensorChannel(channel);
        const key = structuralProgramKey(spec);
        const key_hash = structuralProgramKeyHash(key);
        if (self.tensor_only_index_by_hash.get(key_hash)) |entry_index| {
            if (entry_index < self.tensor_only_entries.items.len) {
                const entry = self.tensor_only_entries.items[entry_index];
                if (structuralProgramKeyEql(entry.key, key)) {
                    self.hits += 1;
                    return &self.tensor_only_entries.items[entry_index].program;
                }
            }
        }
        for (self.tensor_only_entries.items, 0..) |entry, entry_index| {
            if (structuralProgramKeyEql(entry.key, key)) {
                self.hits += 1;
                return &self.tensor_only_entries.items[entry_index].program;
            }
        }
        var program = compileGeneralTensorOnlyBrauerProgram(tensor_channel) catch |err| switch (err) {
            error.UnsupportedTensorBridge => return null,
            error.ProjectorProgramTooLarge => if (tensorChannelRequiresTensorOnlySizeError(channel)) return err else return null,
            else => return err,
        };
        errdefer program.deinit();
        self.misses += 1;
        const entry_index: u32 = @intCast(self.tensor_only_entries.items.len);
        var index_inserted = false;
        if (!self.tensor_only_index_by_hash.contains(key_hash)) {
            try self.tensor_only_index_by_hash.put(key_hash, entry_index);
            index_inserted = true;
        }
        errdefer {
            if (index_inserted) _ = self.tensor_only_index_by_hash.remove(key_hash);
        }
        try self.tensor_only_entries.append(self.allocator, .{ .key = key, .program = program });
        index_inserted = false;
        return &self.tensor_only_entries.items[entry_index].program;
    }

    fn structuralTensorProgramFor(self: *StructuralProjectorProgramCache, channel: TensorCompilerChannel) !?TensorChannelProgram {
        const spec = structuralProjectorSpecFromTensorChannel(channel);
        const key = structuralProgramKey(spec);
        const key_hash = structuralProgramKeyHash(key);
        if (self.tensor_index_by_hash.get(key_hash)) |entry_index| {
            if (entry_index < self.tensor_entries.items.len) {
                const entry = self.tensor_entries.items[entry_index];
                if (structuralProgramKeyEql(entry.key, key)) {
                    self.hits += 1;
                    return entry.program;
                }
            }
        }
        for (self.tensor_entries.items) |entry| {
            if (structuralProgramKeyEql(entry.key, key)) {
                self.hits += 1;
                return entry.program;
            }
        }
        const program = compileFallbackTensorChannelProgram(channel) catch |err| switch (err) {
            error.UnsupportedStructuralProjectorTerm => return null,
            else => return err,
        };
        self.misses += 1;
        const entry_index: u32 = @intCast(self.tensor_entries.items.len);
        try self.tensor_entries.append(self.allocator, .{ .key = key, .program = program });
        if (!self.tensor_index_by_hash.contains(key_hash)) try self.tensor_index_by_hash.put(key_hash, entry_index);
        return program;
    }
};

const Rational = struct {
    numerator: i64,
    denominator: i64,

    fn init(numerator: i64, denominator: i64) !Rational {
        if (denominator == 0) return error.InvalidGramDenominator;
        var out = Rational{ .numerator = numerator, .denominator = denominator };
        out.normalize();
        return out;
    }

    fn zero() Rational {
        return .{ .numerator = 0, .denominator = 1 };
    }

    fn one() Rational {
        return .{ .numerator = 1, .denominator = 1 };
    }

    fn add(self: Rational, other: Rational) !Rational {
        if (self.numerator == 0) return other;
        if (other.numerator == 0) return self;
        const common: i64 = @intCast(gcdU64(absI64(self.denominator), absI64(other.denominator)));
        const left_scale = @divExact(other.denominator, common);
        const right_scale = @divExact(self.denominator, common);
        return Rational.init(try checkedAddI64(
            try checkedMulI64(self.numerator, left_scale),
            try checkedMulI64(other.numerator, right_scale),
        ), try checkedMulI64(self.denominator, left_scale));
    }

    fn sub(self: Rational, other: Rational) !Rational {
        return self.add(.{ .numerator = try checkedNegI64(other.numerator), .denominator = other.denominator });
    }

    fn mul(self: Rational, other: Rational) !Rational {
        if (self.numerator == 0 or other.numerator == 0) return Rational.zero();
        var left_numerator = self.numerator;
        var left_denominator = self.denominator;
        var right_numerator = other.numerator;
        var right_denominator = other.denominator;

        const first_common: i64 = @intCast(gcdU64(absI64(left_numerator), absI64(right_denominator)));
        left_numerator = @divExact(left_numerator, first_common);
        right_denominator = @divExact(right_denominator, first_common);

        const second_common: i64 = @intCast(gcdU64(absI64(right_numerator), absI64(left_denominator)));
        right_numerator = @divExact(right_numerator, second_common);
        left_denominator = @divExact(left_denominator, second_common);

        return Rational.init(try checkedMulI64(left_numerator, right_numerator), try checkedMulI64(left_denominator, right_denominator));
    }

    fn div(self: Rational, other: Rational) !Rational {
        if (other.numerator == 0) return error.SingularGramMatrix;
        return self.mul(.{ .numerator = other.denominator, .denominator = other.numerator });
    }

    fn normalize(self: *Rational) void {
        if (self.numerator == 0) {
            self.denominator = 1;
            return;
        }
        if (self.denominator < 0) {
            self.numerator = -self.numerator;
            self.denominator = -self.denominator;
        }
        const divisor: i64 = @intCast(gcdU64(absI64(self.numerator), absI64(self.denominator)));
        self.numerator = @divExact(self.numerator, divisor);
        self.denominator = @divExact(self.denominator, divisor);
    }
};

const WideRational = struct {
    numerator: i128,
    denominator: i128,

    fn init(numerator: i128, denominator: i128) !WideRational {
        if (denominator == 0) return error.InvalidGramDenominator;
        var out = WideRational{ .numerator = numerator, .denominator = denominator };
        out.normalize();
        return out;
    }

    fn zero() WideRational {
        return .{ .numerator = 0, .denominator = 1 };
    }

    fn one() WideRational {
        return .{ .numerator = 1, .denominator = 1 };
    }

    fn fromRational(value: Rational) WideRational {
        return .{ .numerator = value.numerator, .denominator = value.denominator };
    }

    fn toRational(self: WideRational) !Rational {
        if (self.numerator < std.math.minInt(i64) or self.numerator > std.math.maxInt(i64)) return error.GramIntegerOverflow;
        if (self.denominator <= 0 or self.denominator > std.math.maxInt(i64)) return error.GramIntegerOverflow;
        return Rational.init(@intCast(self.numerator), @intCast(self.denominator));
    }

    fn add(self: WideRational, other: WideRational) !WideRational {
        if (self.numerator == 0) return other;
        if (other.numerator == 0) return self;
        const common: i128 = @intCast(gcdU128(absI128(self.denominator), absI128(other.denominator)));
        const left_scale = @divExact(other.denominator, common);
        const right_scale = @divExact(self.denominator, common);
        return WideRational.init(try checkedAddI128(
            try checkedMulI128(self.numerator, left_scale),
            try checkedMulI128(other.numerator, right_scale),
        ), try checkedMulI128(self.denominator, left_scale));
    }

    fn sub(self: WideRational, other: WideRational) !WideRational {
        return self.add(.{ .numerator = try checkedNegI128(other.numerator), .denominator = other.denominator });
    }

    fn mul(self: WideRational, other: WideRational) !WideRational {
        if (self.numerator == 0 or other.numerator == 0) return WideRational.zero();
        var left_numerator = self.numerator;
        var left_denominator = self.denominator;
        var right_numerator = other.numerator;
        var right_denominator = other.denominator;

        const first_common: i128 = @intCast(gcdU128(absI128(left_numerator), absI128(right_denominator)));
        left_numerator = @divExact(left_numerator, first_common);
        right_denominator = @divExact(right_denominator, first_common);

        const second_common: i128 = @intCast(gcdU128(absI128(right_numerator), absI128(left_denominator)));
        right_numerator = @divExact(right_numerator, second_common);
        left_denominator = @divExact(left_denominator, second_common);

        return WideRational.init(try checkedMulI128(left_numerator, right_numerator), try checkedMulI128(left_denominator, right_denominator));
    }

    fn div(self: WideRational, other: WideRational) !WideRational {
        if (other.numerator == 0) return error.SingularGramMatrix;
        return self.mul(.{ .numerator = other.denominator, .denominator = other.numerator });
    }

    fn normalize(self: *WideRational) void {
        if (self.numerator == 0) {
            self.denominator = 1;
            return;
        }
        if (self.denominator < 0) {
            self.numerator = -self.numerator;
            self.denominator = -self.denominator;
        }
        const divisor: i128 = @intCast(gcdU128(absI128(self.numerator), absI128(self.denominator)));
        self.numerator = @divExact(self.numerator, divisor);
        self.denominator = @divExact(self.denominator, divisor);
    }
};

const ContractionAccumulator = struct {
    coefficient: Rational = .{ .numerator = 1, .denominator = 1 },
    remaining_form_profile: u128 = 0,
    remaining_tower_power: u8 = 0,
    chirality: u8 = 0,
    duality: rendering.DualityTag = .none,
    is_zero: bool = false,
};

const StructuralProgramKey = struct {
    dimension: u16 = 0,
    source_form_profile: u128 = 0,
    target_form_profile: u128 = 0,
    source_young_row_count: u8 = 0,
    source_young_rows: [max_young_rows]u8 = [_]u8{0} ** max_young_rows,
    source_young_box_count: u8 = 0,
    right_young_row_count: u8 = 0,
    right_young_rows: [max_young_rows]u8 = [_]u8{0} ** max_young_rows,
    right_young_box_count: u8 = 0,
    target_young_row_count: u8 = 0,
    target_young_rows: [max_young_rows]u8 = [_]u8{0} ** max_young_rows,
    target_young_box_count: u8 = 0,
    source_tower_power: u16 = 0,
    target_tower_power: u16 = 0,
    source_has_spinor: bool = false,
    right_has_spinor: bool = false,
    target_has_spinor: bool = false,
    source_chirality: u8 = 0,
    right_chirality: u8 = 0,
    target_chirality: u8 = 0,
    duality: rendering.DualityTag = .none,
    signature_sequence_hash: u64 = 0,
};

const GramInverse2 = struct {
    values: [4]Rational,

    fn at(self: GramInverse2, row: usize, column: usize) Rational {
        return self.values[row * 2 + column];
    }
};

fn invertGram2(g00: i64, g01: i64, g11: i64) !GramInverse2 {
    const a = try Rational.init(g00, 1);
    const b = try Rational.init(g01, 1);
    const d = try Rational.init(g11, 1);
    const determinant = try (try a.mul(d)).sub(try b.mul(b));
    if (determinant.numerator == 0) return error.SingularGramMatrix;
    const off_diagonal = try Rational.init(try checkedNegI64(g01), 1);
    return .{ .values = .{
        try d.div(determinant),
        try off_diagonal.div(determinant),
        try off_diagonal.div(determinant),
        try a.div(determinant),
    } };
}

const max_gram_generators = max_program_candidates;

const GramPivotSelection = struct {
    count: u8 = 0,
    pivots: [max_program_pivots]u8 = [_]u8{0} ** max_program_pivots,
};

const RankSplitProfile = struct {
    source_rank: u8,
    lower_rank: u8,
    upper_rank: u8,
    carried_profile: u128,
};

const ProfileRankMove = struct {
    source_rank: u8,
    target_rank: u8,
};

fn selectIndependentGramPivots(dimension: u8, entries: []const Rational) !GramPivotSelection {
    if (dimension > max_program_candidates) return error.UnsupportedTensorBrauerCandidateCap;
    const width: usize = dimension;
    if (entries.len < width * width) return error.InvalidGramMatrixSize;

    var matrix: [max_gram_generators * max_gram_generators]Rational = undefined;
    var row: usize = 0;
    while (row < width) : (row += 1) {
        var column: usize = 0;
        while (column < width) : (column += 1) {
            matrix[row * max_gram_generators + column] = entries[row * width + column];
        }
    }

    var selection: GramPivotSelection = .{};
    var pivot_row: usize = 0;
    var pivot_column: usize = 0;
    while (pivot_column < width and pivot_row < width) : (pivot_column += 1) {
        const source_row = findPivotRow(matrix[0..], width, pivot_row, pivot_column) orelse continue;
        if (selection.count == max_program_pivots) return error.UnsupportedTensorPivotCap;
        if (source_row != pivot_row) swapGramRows(matrix[0..], pivot_row, source_row);

        const pivot = matrix[pivot_row * max_gram_generators + pivot_column];
        row = 0;
        while (row < width) : (row += 1) {
            if (row == pivot_row) continue;
            const value = matrix[row * max_gram_generators + pivot_column];
            if (value.numerator == 0) continue;
            const factor = try value.div(pivot);
            var column = pivot_column;
            while (column < width) : (column += 1) {
                const scaled = try factor.mul(matrix[pivot_row * max_gram_generators + column]);
                matrix[row * max_gram_generators + column] = try matrix[row * max_gram_generators + column].sub(scaled);
            }
        }

        selection.pivots[selection.count] = @intCast(pivot_column);
        selection.count += 1;
        pivot_row += 1;
    }
    return selection;
}

fn findPivotRow(matrix: []const Rational, width: usize, first_row: usize, column: usize) ?usize {
    var row = first_row;
    while (row < width) : (row += 1) {
        if (matrix[row * max_gram_generators + column].numerator != 0) return row;
    }
    return null;
}

fn swapGramRows(matrix: []Rational, left: usize, right: usize) void {
    var column: usize = 0;
    while (column < max_gram_generators) : (column += 1) {
        const left_index = left * max_gram_generators + column;
        const right_index = right * max_gram_generators + column;
        const temporary = matrix[left_index];
        matrix[left_index] = matrix[right_index];
        matrix[right_index] = temporary;
    }
}

fn checkedAddI64(left: i64, right: i64) !i64 {
    return std.math.add(i64, left, right) catch error.GramIntegerOverflow;
}

fn checkedMulI64(left: i64, right: i64) !i64 {
    return std.math.mul(i64, left, right) catch error.GramIntegerOverflow;
}

fn checkedMulU32(left: u32, right: u32) !u32 {
    return std.math.mul(u32, left, right) catch error.ProjectorProgramTooLarge;
}

fn checkedNegI64(value: i64) !i64 {
    return std.math.sub(i64, 0, value) catch error.GramIntegerOverflow;
}

fn checkedAddI128(left: i128, right: i128) !i128 {
    return std.math.add(i128, left, right) catch error.GramIntegerOverflow;
}

fn checkedMulI128(left: i128, right: i128) !i128 {
    return std.math.mul(i128, left, right) catch error.GramIntegerOverflow;
}

fn checkedNegI128(value: i128) !i128 {
    return std.math.sub(i128, 0, value) catch error.GramIntegerOverflow;
}

fn absI64(value: i64) u64 {
    if (value == std.math.minInt(i64)) return @as(u64, 1) << 63;
    return if (value < 0) @intCast(-value) else @intCast(value);
}

fn absI128(value: i128) u128 {
    if (value == std.math.minInt(i128)) return @as(u128, 1) << 127;
    return if (value < 0) @intCast(-value) else @intCast(value);
}

fn gcdU64(left: u64, right: u64) u64 {
    var a = left;
    var b = right;
    while (b != 0) {
        const next = a % b;
        a = b;
        b = next;
    }
    return if (a == 0) 1 else a;
}

fn gcdU128(left: u128, right: u128) u128 {
    var a = left;
    var b = right;
    while (b != 0) {
        const next = a % b;
        a = b;
        b = next;
    }
    return if (a == 0) 1 else a;
}

/// appendTensorFormGammaExpression emits the primitive terminal gamma projector.
pub fn appendTensorFormGammaExpression(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorFormGammaSpec) !void {
    const input_count = profileTotalPower(spec.input_form_profile);
    const rank = inferTerminalGammaRank(spec.input_form_profile, spec.output_form_profile) orelse return error.UnsupportedTensorFormGammaProjector;
    if (rank == 0 or rank > spec.orthogonal_dimension) return error.InvalidTensorFormGammaRank;

    try atoms.append(allocator, .{ .gamma_form = .{
        .operator_id = spec.operator_id,
        .spinor_left = tensorSpinorSpinorIndex(spec.left),
        .spinor_right = spec.right,
        .form = tensorFormInsertedBlock(spec.output, rank),
        .orthogonal_dimension = spec.orthogonal_dimension,
        .rank = rank,
        .chirality = spec.chirality,
    } });
    if (input_count != 0) {
        try atoms.append(allocator, .{ .generalized_delta = .{
            .upper = tensorFormCarriedBlock(spec.left),
            .lower = tensorFormCarriedBlock(spec.output),
        } });
    }
}

/// appendTensorFormProjectionExpression emits explicit tensor-form atoms when supported.
pub fn appendTensorFormProjectionExpression(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorFormProjectionSpec) !bool {
    if (tensorFormProjectionTermCount(spec) == 1) {
        _ = try appendTensorFormProjectionTerm(allocator, atoms, spec, 0);
        return true;
    }

    try appendCompactTensorFormProjection(allocator, atoms, spec);
    return false;
}

/// tensorFormProjectionTermCount returns explicit term count for supported classes.
pub fn tensorFormProjectionTermCount(spec: TensorFormProjectionSpec) u16 {
    return switch (tensorFormProjectionTransition(spec)) {
        .gamma_delta, .rank_split, .middle_dual => structuralProjectorTermCount(structuralProjectorSpecFromTensorForm(spec)),
        .unsupported => 0,
    };
}

/// appendTensorFormProjectionTerm emits one explicit term for a supported class.
pub fn appendTensorFormProjectionTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorFormProjectionSpec, term_index: u16) !rendering.RationalId {
    return switch (tensorFormProjectionTransition(spec)) {
        .gamma_delta, .rank_split, .middle_dual => appendStructuralProjectorTerm(allocator, atoms, structuralProjectorSpecFromTensorForm(spec), term_index),
        .unsupported => error.UnsupportedTensorFormProjectionTerm,
    };
}

/// appendTensorSpinorProjectionExpression emits explicit tensor-spinor atoms when supported.
pub fn appendTensorSpinorProjectionExpression(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorSpinorProjectionSpec) !bool {
    if (tensorSpinorProjectionTermCount(spec) == 1) {
        _ = try appendTensorSpinorProjectionTerm(allocator, atoms, spec, 0);
        return true;
    }

    try appendCompactTensorSpinorProjection(allocator, atoms, spec);
    return false;
}

/// tensorSpinorProjectionTermCount returns explicit term count for supported classes.
pub fn tensorSpinorProjectionTermCount(spec: TensorSpinorProjectionSpec) u16 {
    return structuralProjectorTermCount(structuralProjectorSpecFromTensorSpinor(spec));
}

/// appendTensorSpinorProjectionTerm emits one explicit term for a supported class.
pub fn appendTensorSpinorProjectionTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorSpinorProjectionSpec, term_index: u16) !rendering.RationalId {
    return appendStructuralProjectorTerm(allocator, atoms, structuralProjectorSpecFromTensorSpinor(spec), term_index);
}

fn appendCompactTensorSpinorProjection(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorSpinorProjectionSpec) !void {
    try atoms.append(allocator, .{ .tensor_spinor_projection = .{
        .operator_id = spec.operator_id,
        .left = spec.left,
        .right = spec.right,
        .output = spec.output,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .left_has_spinor = spec.left_has_spinor,
        .right_has_spinor = spec.right_has_spinor,
        .output_has_spinor = spec.output_has_spinor,
        .right_chirality = spec.right_chirality,
        .input_form_profile = spec.input_form_profile,
        .input_form_count = spec.input_form_count,
        .input_tower_power = spec.input_tower_power,
        .form_rank = spec.form_rank,
        .form_count = spec.form_count,
        .form_mask = spec.form_mask,
        .form_profile = spec.form_profile,
        .tower_power = spec.tower_power,
        .chirality = spec.chirality,
        .duality = spec.duality,
    } });
}

fn appendCompactTensorFormProjection(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorFormProjectionSpec) !void {
    try atoms.append(allocator, .{ .tensor_form_projection = .{
        .operator_id = spec.operator_id,
        .left = spec.left,
        .right = spec.right,
        .output = spec.output,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .input_form_profile = spec.input_form_profile,
        .input_form_mask = spec.input_form_mask,
        .output_form_profile = spec.output_form_profile,
        .output_form_count = spec.output_form_count,
        .output_form_rank = spec.output_form_rank,
        .output_duality = spec.output_duality,
        .right_chirality = spec.right_chirality,
        .chirality = spec.chirality,
    } });
}

fn appendTensorFormGammaTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorFormProjectionSpec, term_index: u16) !rendering.RationalId {
    if (term_index != 0) return error.ProjectorConstructorTermOutOfBounds;
    try appendTensorFormGammaExpression(allocator, atoms, .{
        .operator_id = spec.operator_id,
        .left = spec.left,
        .right = spec.right,
        .output = spec.output,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .input_form_profile = spec.input_form_profile,
        .output_form_profile = spec.output_form_profile,
        .chirality = spec.chirality,
    });
    return rendering.rationalOne();
}

/// structuralProjectorTermCount returns the streamed term count for a structural channel.
pub fn structuralProjectorTermCount(spec: StructuralProjectorSpec) u16 {
    if (tensorCompilerChannelFromStructuralOrNull(spec) catch null) |channel| {
        if (tensorChannelUsesDirectStructuralProgram(channel)) {
            const program = compileStructuralProjectorProgram(spec) catch return 0;
            return projectorProgramTermCount(program);
        }
        if (tensorChannelTermCount(channel) catch null) |count| {
            if (count != 0 or !tensorChannelStructuralFallbackAllowed(channel)) return count;
        }
        if (!tensorChannelStructuralFallbackAllowed(channel)) return 0;
    }
    const program = compileStructuralProjectorProgram(spec) catch return 0;
    return projectorProgramTermCount(program);
}

/// appendStructuralProjectorTerm emits one exact structural projector program term.
pub fn appendStructuralProjectorTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: StructuralProjectorSpec, term_index: u16) !rendering.RationalId {
    if (try tensorCompilerChannelFromStructuralOrNull(spec)) |channel| {
        if (tensorChannelUsesDirectStructuralProgram(channel)) {
            const program = try compileStructuralProjectorProgram(spec);
            return appendStructuralProjectorProgramTerm(allocator, atoms, spec, program, term_index);
        }
        const coefficient: ?rendering.RationalId = appendTensorChannelTerm(allocator, atoms, channel, term_index) catch |err| switch (err) {
            error.UnsupportedTensorBridge => null,
            else => return err,
        };
        if (coefficient) |value| return value;
        if (!tensorChannelStructuralFallbackAllowed(channel)) return error.UnsupportedTensorBridge;
    }
    const program = try compileStructuralProjectorProgram(spec);
    return appendStructuralProjectorProgramTerm(allocator, atoms, spec, program, term_index);
}

fn tensorCompilerChannelFromStructuralOrNull(spec: StructuralProjectorSpec) anyerror!?TensorCompilerChannel {
    return tensorCompilerChannelFromStructural(spec) catch |err| switch (err) {
        error.UnsupportedTensorShapeOverCap, error.InvalidYoungShape, error.InvalidFormProfile => if (structuralSpecHasSpinor(spec)) null else return err,
        else => null,
    };
}

fn structuralSpecHasSpinor(spec: StructuralProjectorSpec) bool {
    return spec.left.has_spinor or spec.right.has_spinor or spec.output.has_spinor;
}

fn tensorChannelKind(channel: TensorCompilerChannel) !TensorChannelKind {
    if (youngOutputApplies(channel)) return .young_output;
    if (scalarPairingApplies(channel)) return .scalar_pairing;
    if (tensorContractionApplies(channel)) return .tensor_contraction;
    if (compressedFormBridgeApplies(channel)) return .compressed_form_bridge;
    if (spinorCliffordBridgeApplies(channel)) return .spinor_clifford_bridge;
    return error.UnsupportedTensorBridge;
}

fn tensorChannelStructuralFallbackAllowed(channel: TensorCompilerChannel) bool {
    return spinorCliffordBridgeApplies(channel);
}

fn tensorChannelUsesDirectStructuralProgram(channel: TensorCompilerChannel) bool {
    return spinorCliffordBridgeApplies(channel);
}

fn youngOutputApplies(channel: TensorCompilerChannel) bool {
    return vectorSlotProjectorSpecFromChannel(channel) != null;
}

fn scalarPairingApplies(channel: TensorCompilerChannel) bool {
    return tensorPairingSpecFromChannel(channel) != null;
}

fn tensorContractionApplies(channel: TensorCompilerChannel) bool {
    return tensorContractionSpecFromChannel(channel) != null;
}

fn compressedFormBridgeApplies(channel: TensorCompilerChannel) bool {
    return !channel.left.descriptor.has_spinor and
        !channel.right.descriptor.has_spinor and
        !channel.output.descriptor.has_spinor and
        (channel.left.descriptor.kind == .mixed_tensor_form or
            channel.right.descriptor.kind == .mixed_tensor_form or
            channel.output.descriptor.kind == .mixed_tensor_form);
}

fn tensorChannelRequiresTensorOnlySizeError(channel: TensorCompilerChannel) bool {
    if (spinorCliffordBridgeApplies(channel)) return false;
    return tensorEndpointRequiresTensorOnlySizeError(channel.left) or
        tensorEndpointRequiresTensorOnlySizeError(channel.right) or
        tensorEndpointRequiresTensorOnlySizeError(channel.output);
}

fn tensorEndpointRequiresTensorOnlySizeError(endpoint: ExplicitEndpoint) bool {
    return endpoint.descriptor.kind == .mixed_tensor_form or endpoint.descriptor.form_duality != .none;
}

fn spinorCliffordBridgeApplies(channel: TensorCompilerChannel) bool {
    return channel.left.descriptor.has_spinor or
        channel.right.descriptor.has_spinor or
        channel.output.descriptor.has_spinor;
}

fn tensorChannelTermCount(channel: TensorCompilerChannel) !u16 {
    if (liveTensorOnlyChannelFromCompilerChannel(channel)) |tensor_channel| {
        const program = compileGeneralTensorOnlyBrauerProgram(tensor_channel) catch |err| switch (err) {
            error.UnsupportedTensorBridge => null,
            error.ProjectorProgramTooLarge => if (tensorChannelRequiresTensorOnlySizeError(channel)) return err else null,
            else => return err,
        };
        if (program) |compiled_program| {
            var tensor_program = compiled_program;
            defer tensor_program.deinit();
            return tensor_program.term_count;
        }
    } else |err| switch (err) {
        error.UnsupportedTensorBridge => {},
        else => return err,
    }
    if (try tensorChannelKind(channel) == .compressed_form_bridge) return error.UnsupportedTensorBridge;
    const program = try compileFallbackTensorChannelProgram(channel);
    return program.term_count;
}

fn appendTensorChannelTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), channel: TensorCompilerChannel, term_index: u16) !rendering.RationalId {
    if (liveTensorOnlyChannelFromCompilerChannel(channel)) |tensor_channel| {
        const program = compileGeneralTensorOnlyBrauerProgram(tensor_channel) catch |err| switch (err) {
            error.UnsupportedTensorBridge => null,
            error.ProjectorProgramTooLarge => if (tensorChannelRequiresTensorOnlySizeError(channel)) return err else null,
            else => return err,
        };
        if (program) |compiled_program| {
            var tensor_program = compiled_program;
            defer tensor_program.deinit();
            return appendTensorOnlyProgramTerm(allocator, atoms, &tensor_program, term_index);
        }
    } else |err| switch (err) {
        error.UnsupportedTensorBridge => {},
        else => return err,
    }
    if (try tensorChannelKind(channel) == .compressed_form_bridge) return error.UnsupportedTensorBridge;
    const program = try compileFallbackTensorChannelProgram(channel);
    return appendTensorChannelProgramTerm(allocator, atoms, program, term_index);
}

fn compileDiagnosticFallbackTensorChannelProgram(channel: TensorCompilerChannel) !TensorChannelProgram {
    return compileFallbackTensorChannelProgram(channel);
}

fn compileFallbackTensorChannelProgram(channel: TensorCompilerChannel) !TensorChannelProgram {
    var program = try initTensorChannelProgram(channel);
    var candidates: TensorCandidateBuffer = .{};
    try enumerateTensorCandidates(channel, &program, &candidates);
    try installTensorCandidateWords(&program, candidates);
    try finishTensorChannelProgram(&program);
    return program;
}

fn initTensorChannelProgram(channel: TensorCompilerChannel) !TensorChannelProgram {
    return switch (try tensorChannelKind(channel)) {
        .young_output => initVectorBackedTensorChannelProgram(.projector, vectorSlotProjectorSpecFromChannel(channel).?),
        .scalar_pairing => initVectorBackedTensorChannelProgram(.pairing, vectorProjectorSpecForPairing(tensorPairingSpecFromChannel(channel).?)),
        .tensor_contraction => initVectorBackedTensorContractionProgram(tensorContractionSpecFromChannel(channel).?),
        .compressed_form_bridge => initStructuralBackedTensorChannelProgram(structuralProjectorSpecFromTensorChannel(channel)) catch |err| switch (err) {
            error.UnsupportedStructuralProjectorTerm => error.UnsupportedTensorBridge,
            else => err,
        },
        .spinor_clifford_bridge => initStructuralBackedTensorChannelProgram(structuralProjectorSpecFromTensorChannel(channel)),
    };
}

fn initVectorBackedTensorChannelProgram(kind: CachedVectorProgramKind, spec: VectorSlotProjectorSpec) !TensorChannelProgram {
    var program: TensorChannelProgram = .{
        .kind = kind,
        .dimension = spec.dimension,
        .rank = vectorYoungRank(spec) orelse return error.UnsupportedStructuralProjectorTerm,
        .vector_spec = spec,
    };
    program.vector_program = try compileVectorYoungBrauerCore(spec);
    return program;
}

fn compileVectorBackedTensorChannelProgram(kind: CachedVectorProgramKind, spec: VectorSlotProjectorSpec) !TensorChannelProgram {
    var program = try initVectorBackedTensorChannelProgram(kind, spec);
    var candidates: TensorCandidateBuffer = .{};
    try enumerateVectorBackedTensorCandidates(&candidates, kind, spec, program.vector_program.candidate_count);
    try installTensorCandidateWords(&program, candidates);
    try finishTensorChannelProgram(&program);
    return program;
}

fn enumerateTensorCandidates(channel: TensorCompilerChannel, program: *const TensorChannelProgram, out: *TensorCandidateBuffer) !void {
    switch (try tensorChannelKind(channel)) {
        .young_output => try enumerateVectorBackedTensorCandidates(out, .projector, program.vector_spec, program.vector_program.candidate_count),
        .scalar_pairing => try enumerateVectorBackedTensorCandidates(out, .pairing, program.vector_spec, program.vector_program.candidate_count),
        .tensor_contraction => try enumerateVectorBackedTensorCandidates(out, .contraction, program.vector_spec, program.vector_program.candidate_count),
        .compressed_form_bridge, .spinor_clifford_bridge => try enumerateStructuralTensorCandidates(out, program.candidate_count),
    }
}

fn enumerateVectorBackedTensorCandidates(out: *TensorCandidateBuffer, kind: CachedVectorProgramKind, spec: VectorSlotProjectorSpec, candidate_count: u8) !void {
    var candidate_index: u8 = 0;
    while (candidate_index < candidate_count) : (candidate_index += 1) {
        var word: TensorCandidateWord = .{};
        try appendTensorVectorBridgePrimitives(&word, spec);
        try word.append(.{
            .kind = switch (kind) {
                .projector => .vector_young_output,
                .pairing => .vector_young_pairing,
                .contraction => .vector_tensor_contraction,
                .structural => return error.UnsupportedTensorBridge,
            },
            .candidate_index = candidate_index,
        });
        try out.append(word);
    }
}

fn enumerateStructuralTensorCandidates(out: *TensorCandidateBuffer, candidate_count: u8) !void {
    var candidate_index: u8 = 0;
    while (candidate_index < candidate_count) : (candidate_index += 1) {
        var word: TensorCandidateWord = .{};
        try word.append(.{
            .kind = .structural_projection,
            .candidate_index = candidate_index,
        });
        try out.append(word);
    }
}

fn installTensorCandidateWords(program: *TensorChannelProgram, candidates: TensorCandidateBuffer) !void {
    if (candidates.count == 0) return error.UnsupportedStructuralProjectorTerm;
    program.candidate_count = candidates.count;
    program.words = candidates.words;
}

fn finishTensorChannelProgram(program: *TensorChannelProgram) !void {
    try compileTensorWordGram(program);
    program.term_count = try countTensorChannelProgramTerms(program.*);
    if (program.term_count == 0) return error.UnsupportedStructuralProjectorTerm;
}

fn appendTensorVectorBridgePrimitives(word: *TensorCandidateWord, spec: VectorSlotProjectorSpec) !void {
    if (spec.left_form_profile != 0) {
        const slot_count = try profileVectorSlotCount(spec.left_form_profile);
        if (slot_count != spec.left_slot_count) return error.UnsupportedTensorBridge;
        try word.append(.{ .kind = .form_bridge, .candidate_index = 0 });
    }
    if (spec.right_form_profile != 0) {
        const slot_count = try profileVectorSlotCount(spec.right_form_profile);
        if (slot_count != spec.right_slot_count) return error.UnsupportedTensorBridge;
        try word.append(.{ .kind = .form_bridge, .candidate_index = 1 });
    }
    if (spec.output_form_profile != 0) {
        const slot_count = try profileVectorSlotCount(spec.output_form_profile);
        if (slot_count != spec.shape.box_count) return error.UnsupportedTensorBridge;
        try word.append(.{ .kind = .form_bridge, .candidate_index = 2 });
    }
}

fn appendTensorChannelProgramTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), program: TensorChannelProgram, term_index: u16) !rendering.RationalId {
    if (program.kind == .structural) return appendTensorStructuralProgramTerm(allocator, atoms, program, term_index);
    const term = try tensorChannelProgramTermAt(program, term_index);
    return switch (program.kind) {
        .projector => appendVectorBrauerTermAtoms(allocator, atoms, term),
        .pairing => appendTensorPairingBrauerTermAtoms(allocator, atoms, term),
        .contraction => appendVectorBrauerTermAtoms(allocator, atoms, term),
        .structural => unreachable,
    };
}

fn initVectorBackedTensorContractionProgram(spec: TensorContractionSpec) !TensorChannelProgram {
    var program: TensorChannelProgram = .{
        .kind = .contraction,
        .dimension = spec.dimension,
        .rank = spec.left_slot_count + spec.right_slot_count,
        .vector_spec = vectorProjectorSpecForContraction(spec),
    };
    program.vector_program = try compileTensorContractionBrauerCore(spec);
    return program;
}

fn compileVectorBackedTensorContractionProgram(spec: TensorContractionSpec) !TensorChannelProgram {
    var program = try initVectorBackedTensorContractionProgram(spec);
    var candidates: TensorCandidateBuffer = .{};
    try enumerateVectorBackedTensorCandidates(&candidates, .contraction, program.vector_spec, program.vector_program.candidate_count);
    try installTensorCandidateWords(&program, candidates);
    try finishTensorChannelProgram(&program);
    return program;
}

fn initStructuralBackedTensorChannelProgram(spec: StructuralProjectorSpec) !TensorChannelProgram {
    const candidates = try enumerateOrthogonalStructuralCandidateWords(spec);
    if (candidates.count == 0) return error.UnsupportedStructuralProjectorTerm;
    if (candidates.count > max_program_candidates) return error.UnsupportedTensorBrauerCandidateCap;

    return .{
        .kind = .structural,
        .dimension = spec.orthogonal_dimension,
        .structural_spec = spec,
        .candidate_count = candidates.count,
        .structural_candidates = candidates.words,
    };
}

fn compileStructuralBackedTensorChannelProgram(spec: StructuralProjectorSpec) !TensorChannelProgram {
    var program = try initStructuralBackedTensorChannelProgram(spec);
    var candidates: TensorCandidateBuffer = .{};
    try enumerateStructuralTensorCandidates(&candidates, program.candidate_count);
    try installTensorCandidateWords(&program, candidates);
    try finishTensorChannelProgram(&program);
    return program;
}

fn structuralProjectorSpecFromTensorChannel(channel: TensorCompilerChannel) StructuralProjectorSpec {
    return .{
        .operator_id = channel.operator_id,
        .orthogonal_dimension = channel.dimension,
        .left = structuralEndpointFromExplicit(channel.left),
        .right = structuralEndpointFromExplicit(channel.right),
        .output = structuralEndpointFromExplicit(channel.output),
    };
}

fn structuralEndpointFromExplicit(endpoint: ExplicitEndpoint) StructuralEndpoint {
    return .{
        .index = endpoint.block,
        .form_profile = endpoint.descriptor.form_profile,
        .form_mask = endpoint.descriptor.form_mask,
        .form_count = @intCast(profileTotalPower(endpoint.descriptor.form_profile)),
        .form_rank = endpoint.descriptor.form_rank,
        .form_duality = endpoint.descriptor.form_duality,
        .young_row_count = endpoint.descriptor.young_row_count,
        .young_rows = endpoint.descriptor.young_rows,
        .young_box_count = endpoint.descriptor.young_box_count,
        .tower_power = endpoint.descriptor.tower_power,
        .chirality = endpoint.descriptor.chirality,
        .has_spinor = endpoint.descriptor.has_spinor,
    };
}

fn appendTensorStructuralProgramTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), program: TensorChannelProgram, term_index: u16) !rendering.RationalId {
    if (term_index >= program.term_count) return error.ProjectorConstructorTermOutOfBounds;
    var seen: u16 = 0;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
            if (coefficient.numerator == 0) continue;
            const left_index = program.pivots[row];
            const right_index = program.pivots[column];
            const pair_count = try countTensorWordPairTerms(program, program.words[left_index], program.words[right_index], coefficient);
            if (term_index < seen + pair_count) {
                const scaled = try tensorWordPairCoefficient(program.words[left_index], program.words[right_index], coefficient);
                if (scaled.numerator == 0) return error.ProjectorConstructorTermOutOfBounds;
                try appendStructuralCandidateWordAtoms(allocator, atoms, program.structural_spec, program.structural_candidates[left_index]);
                try appendStructuralCandidateWordAdjointAtoms(allocator, atoms, program.structural_spec, program.structural_candidates[right_index]);
                return rationalToRenderingId(scaled);
            }
            seen += pair_count;
        }
    }
    return error.ProjectorConstructorTermOutOfBounds;
}

fn tensorCandidateInnerProduct(program: TensorChannelProgram, left: TensorCandidateWord, right: TensorCandidateWord) !Rational {
    const expected_kind: TensorPrimitiveKind = switch (program.kind) {
        .projector => .vector_young_output,
        .pairing => .vector_young_pairing,
        .contraction => .vector_tensor_contraction,
        .structural => .structural_projection,
    };

    if (program.kind == .structural) {
        const left_candidate_index = try tensorWordStructuralCandidateIndex(&program, left);
        const right_candidate_index = try tensorWordStructuralCandidateIndex(&program, right);
        var value = try structuralCandidateInnerProduct(
            program.structural_candidates[left_candidate_index],
            program.structural_candidates[right_candidate_index],
        );
        value = try value.mul(left.coefficient);
        value = try value.mul(right.coefficient);
        return value;
    }

    const left_candidate_index = try tensorWordVectorCandidateIndex(&program, left, expected_kind);
    const right_candidate_index = try tensorWordVectorCandidateIndex(&program, right, expected_kind);
    if (program.kind == .contraction) {
        var value = try tensorContractionCandidateInnerProduct(
            tensorContractionSpecFromVectorSpec(program.vector_spec),
            program.vector_program.candidates[left_candidate_index],
            program.vector_program.candidates[right_candidate_index],
        );
        value = try value.mul(left.coefficient);
        value = try value.mul(right.coefficient);
        return value;
    }
    var value = try brauerCandidateInnerProduct(
        program.dimension,
        program.rank,
        program.vector_program.candidates[left_candidate_index],
        program.vector_program.candidates[right_candidate_index],
    );
    value = try value.mul(left.coefficient);
    value = try value.mul(right.coefficient);
    return value;
}

fn compileTensorWordGram(program: *TensorChannelProgram) !void {
    var gram: [max_program_candidate_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_program_candidate_gram_entries;
    var row: usize = 0;
    while (row < program.candidate_count) : (row += 1) {
        var column: usize = 0;
        while (column <= row) : (column += 1) {
            const value = try tensorCandidateInnerProduct(program.*, program.words[row], program.words[column]);
            gram[row * program.candidate_count + column] = value;
            gram[column * program.candidate_count + row] = value;
        }
    }

    const pivots = try selectIndependentGramPivots(program.candidate_count, gram[0..]);
    if (pivots.count == 0) return error.SingularGramMatrix;
    if (pivots.count > max_program_pivots) return error.UnsupportedTensorPivotCap;
    var pivot_gram: [max_program_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_program_gram_entries;
    row = 0;
    while (row < pivots.count) : (row += 1) {
        var column: usize = 0;
        while (column < pivots.count) : (column += 1) {
            pivot_gram[row * pivots.count + column] = gram[@as(usize, pivots.pivots[row]) * program.candidate_count + pivots.pivots[column]];
        }
    }

    program.pivot_count = pivots.count;
    var pivot_index: u8 = 0;
    while (pivot_index < pivots.count) : (pivot_index += 1) {
        program.pivots[pivot_index] = pivots.pivots[pivot_index];
    }
    program.inverse_gram = try invertSmallGram(pivots.count, pivot_gram[0..]);
}

fn tensorChannelProgramTermAt(program: TensorChannelProgram, term_index: u16) !VectorBrauerTerm {
    if (term_index >= program.term_count) return error.ProjectorConstructorTermOutOfBounds;
    var seen: u16 = 0;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
            if (coefficient.numerator == 0) continue;
            const left_index = program.pivots[row];
            const right_index = program.pivots[column];
            const pair_count = try countTensorWordPairTerms(program, program.words[left_index], program.words[right_index], coefficient);
            if (term_index < seen + pair_count) {
                return tensorWordPairTermAt(program, program.words[left_index], program.words[right_index], coefficient, term_index - seen);
            }
            seen += pair_count;
        }
    }
    return error.ProjectorConstructorTermOutOfBounds;
}

fn materializeTensorChannelProgramTerms(program: *const TensorChannelProgram) !VectorBrauerProgram {
    var merged: VectorBrauerProgram = .{};
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
            if (coefficient.numerator == 0) continue;
            const left_index = program.pivots[row];
            const right_index = program.pivots[column];
            try appendTensorWordPairTerms(&merged, program, program.words[left_index], program.words[right_index], coefficient);
        }
    }
    return merged;
}

fn countTensorChannelProgramTerms(program: TensorChannelProgram) !u16 {
    var count: u32 = 0;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
            if (coefficient.numerator == 0) continue;
            const left_index = program.pivots[row];
            const right_index = program.pivots[column];
            count += try countTensorWordPairTerms(program, program.words[left_index], program.words[right_index], coefficient);
            if (count > std.math.maxInt(u16)) return error.ProjectorProgramTooLarge;
        }
    }
    return @intCast(count);
}

fn countTensorWordPairTerms(program: TensorChannelProgram, left: TensorCandidateWord, right: TensorCandidateWord, coefficient: Rational) !u16 {
    if (coefficient.numerator == 0) return 0;
    if (program.kind == .structural) {
        const pair = try tensorStructuralWordPairCandidates(&program, left, right);
        _ = pair;
        const scaled = try tensorWordPairCoefficient(left, right, coefficient);
        return if (scaled.numerator == 0) 0 else 1;
    }
    const pair = try tensorWordPairCandidates(&program, left, right);
    const left_candidate = program.vector_program.candidates[pair.left_candidate];
    const right_candidate = program.vector_program.candidates[pair.right_candidate];
    var count: u16 = 0;
    var left_word_index: u8 = 0;
    while (left_word_index < left_candidate.word_count) : (left_word_index += 1) {
        var right_word_index: u8 = 0;
        while (right_word_index < right_candidate.word_count) : (right_word_index += 1) {
            var word_coefficient = try coefficient.mul(left.coefficient);
            word_coefficient = try word_coefficient.mul(right.coefficient);
            word_coefficient = try word_coefficient.mul(left_candidate.words[left_word_index].coefficient);
            word_coefficient = try word_coefficient.mul(right_candidate.words[right_word_index].coefficient);
            if (word_coefficient.numerator == 0) continue;
            if (count == std.math.maxInt(u16)) return error.ProjectorProgramTooLarge;
            count += 1;
        }
    }
    return count;
}

fn tensorWordPairCoefficient(left: TensorCandidateWord, right: TensorCandidateWord, coefficient: Rational) !Rational {
    var scaled = try coefficient.mul(left.coefficient);
    scaled = try scaled.mul(right.coefficient);
    return scaled;
}

fn appendTensorWordPairTerms(out: *VectorBrauerProgram, program: *const TensorChannelProgram, left: TensorCandidateWord, right: TensorCandidateWord, coefficient: Rational) !void {
    const pair = try tensorWordPairCandidates(program, left, right);

    var scaled = try coefficient.mul(left.coefficient);
    scaled = try scaled.mul(right.coefficient);
    if (program.kind == .contraction) {
        try appendMaterializedTensorContractionPairTerms(
            out,
            tensorProgramVectorSpec(program),
            program.vector_program,
            pair.left_candidate,
            pair.right_candidate,
            scaled,
        );
        return;
    }
    try appendMaterializedVectorBrauerPairTerms(
        out,
        tensorProgramVectorSpec(program),
        program.vector_program,
        pair.left_candidate,
        pair.right_candidate,
        scaled,
    );
}

fn tensorWordPairTermAt(program: TensorChannelProgram, left: TensorCandidateWord, right: TensorCandidateWord, coefficient: Rational, term_index: u16) !VectorBrauerTerm {
    const pair = try tensorWordPairCandidates(&program, left, right);
    const left_candidate = program.vector_program.candidates[pair.left_candidate];
    const right_candidate = program.vector_program.candidates[pair.right_candidate];
    var seen: u16 = 0;
    var left_word_index: u8 = 0;
    while (left_word_index < left_candidate.word_count) : (left_word_index += 1) {
        var right_word_index: u8 = 0;
        while (right_word_index < right_candidate.word_count) : (right_word_index += 1) {
            var word_coefficient = try coefficient.mul(left.coefficient);
            word_coefficient = try word_coefficient.mul(right.coefficient);
            word_coefficient = try word_coefficient.mul(left_candidate.words[left_word_index].coefficient);
            word_coefficient = try word_coefficient.mul(right_candidate.words[right_word_index].coefficient);
            if (word_coefficient.numerator == 0) continue;
            if (seen == term_index) {
                if (program.kind == .contraction) {
                    return materializeTensorContractionWordPairTerm(
                        tensorProgramVectorSpec(&program),
                        left_candidate.words[left_word_index],
                        right_candidate.words[right_word_index],
                        word_coefficient,
                    );
                }
                return materializeVectorBrauerWordPairTerm(tensorProgramVectorSpec(&program), left_candidate.words[left_word_index], right_candidate.words[right_word_index], word_coefficient);
            }
            seen += 1;
        }
    }
    return error.ProjectorConstructorTermOutOfBounds;
}

const TensorWordPairCandidateIndices = struct {
    left_candidate: u8,
    right_candidate: u8,
};

fn tensorStructuralWordPairCandidates(program: *const TensorChannelProgram, left: TensorCandidateWord, right: TensorCandidateWord) !TensorWordPairCandidateIndices {
    return .{
        .left_candidate = try tensorWordStructuralCandidateIndex(program, left),
        .right_candidate = try tensorWordStructuralCandidateIndex(program, right),
    };
}

fn tensorWordPairCandidates(program: *const TensorChannelProgram, left: TensorCandidateWord, right: TensorCandidateWord) !TensorWordPairCandidateIndices {
    const expected_kind: TensorPrimitiveKind = switch (program.kind) {
        .projector => .vector_young_output,
        .pairing => .vector_young_pairing,
        .contraction => .vector_tensor_contraction,
        .structural => return error.UnsupportedTensorBridge,
    };
    return .{
        .left_candidate = try tensorWordVectorCandidateIndex(program, left, expected_kind),
        .right_candidate = try tensorWordVectorCandidateIndex(program, right, expected_kind),
    };
}

fn tensorWordVectorCandidateIndex(program: *const TensorChannelProgram, word: TensorCandidateWord, expected_kind: TensorPrimitiveKind) !u8 {
    var found = false;
    var candidate_index: u8 = 0;
    var primitive_index: u8 = 0;
    while (primitive_index < word.primitive_count) : (primitive_index += 1) {
        const primitive = word.primitives[primitive_index];
        if (primitive.kind == .form_bridge) continue;
        if (primitive.kind != expected_kind) return error.UnsupportedTensorBridge;
        if (found) return error.UnsupportedTensorBridge;
        found = true;
        candidate_index = primitive.candidate_index;
    }
    if (!found) return error.UnsupportedTensorBridge;
    if (candidate_index >= program.vector_program.candidate_count) return error.ProjectorConstructorTermOutOfBounds;
    return candidate_index;
}

fn tensorWordStructuralCandidateIndex(program: *const TensorChannelProgram, word: TensorCandidateWord) !u8 {
    if (word.primitive_count != 1) return error.UnsupportedTensorBridge;
    const primitive = word.primitives[0];
    if (primitive.kind != .structural_projection) return error.UnsupportedTensorBridge;
    if (primitive.candidate_index >= program.candidate_count) return error.ProjectorConstructorTermOutOfBounds;
    return primitive.candidate_index;
}

fn tensorProgramVectorSpec(program: *const TensorChannelProgram) VectorSlotProjectorSpec {
    return program.vector_spec;
}

fn vectorProgramRank(program: VectorBrauerProgram) ?u8 {
    if (program.candidate_count == 0) return null;
    const first = program.candidates[0];
    if (first.word_count == 0) return null;
    const rank = first.words[0].edge_count;
    var candidate_index: u8 = 0;
    while (candidate_index < program.candidate_count) : (candidate_index += 1) {
        const candidate = program.candidates[candidate_index];
        var word_index: u8 = 0;
        while (word_index < candidate.word_count) : (word_index += 1) {
            if (candidate.words[word_index].edge_count != rank) return null;
        }
    }
    return rank;
}

fn tensorCompilerChannelFromStructural(spec: StructuralProjectorSpec) anyerror!TensorCompilerChannel {
    const left_descriptor = try tensorDescriptorFromStructuralEndpoint(spec.left, spec.orthogonal_dimension);
    const right_descriptor = try tensorDescriptorFromStructuralEndpoint(spec.right, spec.orthogonal_dimension);
    const output_descriptor = try tensorDescriptorFromStructuralEndpoint(spec.output, spec.orthogonal_dimension);
    return .{
        .operator_id = spec.operator_id,
        .dimension = spec.orthogonal_dimension,
        .left = try explicitEndpoint(.left, spec.left.index, left_descriptor),
        .right = try explicitEndpoint(.right, spec.right.index, right_descriptor),
        .output = try explicitEndpoint(.output, spec.output.index, output_descriptor),
    };
}

fn tensorOnlyChannelFromCompilerChannel(channel: TensorCompilerChannel) !TensorOnlyChannel {
    if (channel.left.has_spinor or channel.right.has_spinor or channel.output.has_spinor) return error.UnsupportedTensorBridge;
    const left = try tensorOnlyEndpointFromExplicit(channel.left);
    const right = try tensorOnlyEndpointFromExplicit(channel.right);
    const output = try tensorOnlyEndpointFromExplicit(channel.output);
    const input_slot_count = left.slot_count + right.slot_count;
    return .{
        .operator_id = channel.operator_id,
        .dimension = channel.dimension,
        .left = left,
        .right = right,
        .output = output,
        .input_slot_count = input_slot_count,
        .output_slot_count = output.slot_count,
    };
}

fn liveTensorOnlyChannelFromCompilerChannel(channel: TensorCompilerChannel) !TensorOnlyChannel {
    const tensor_channel = try tensorOnlyChannelFromCompilerChannel(channel);
    if (!tensorOnlyEndpointLiveRouteSupported(tensor_channel.left)) return error.UnsupportedTensorBridge;
    if (!tensorOnlyEndpointLiveRouteSupported(tensor_channel.right)) return error.UnsupportedTensorBridge;
    if (!tensorOnlyEndpointLiveRouteSupported(tensor_channel.output)) return error.UnsupportedTensorBridge;
    return tensor_channel;
}

fn tensorOnlyEndpointLiveRouteSupported(endpoint: TensorOnlyEndpoint) bool {
    return switch (endpoint.kind) {
        .scalar, .vector_young, .exterior_form, .mixed_tensor_form, .hodge_form => true,
    };
}

fn tensorOnlyEndpointFromExplicit(endpoint: ExplicitEndpoint) !TensorOnlyEndpoint {
    const descriptor = endpoint.descriptor;
    if (descriptor.has_spinor) return error.UnsupportedTensorBridge;
    const slot_count = try descriptorTensorOnlySlotCount(descriptor);
    if (slot_count > max_tensor_slots) return error.UnsupportedTensorShapeOverCap;
    const layout = try tensorOnlyEndpointLayout(endpoint.block, descriptor, slot_count);
    return .{
        .side = endpoint.side,
        .block = endpoint.block,
        .kind = try tensorOnlyEndpointKind(descriptor),
        .slot_count = slot_count,
        .layout = layout,
        .rows = descriptor.young_rows,
        .row_count = descriptor.young_row_count,
        .column_heights = descriptor.column_heights,
        .column_count = descriptor.column_count,
        .form_profile = descriptor.form_profile,
        .form_mask = descriptor.form_mask,
        .form_rank = descriptor.form_rank,
        .duality = descriptor.form_duality,
    };
}

fn tensorOnlyEndpointLayout(block: rendering.IndexRef, descriptor: OrthogonalTensorDescriptor, slot_count: u8) !TensorOnlyEndpointLayout {
    var layout: TensorOnlyEndpointLayout = .{ .slot_count = slot_count };
    var slot: u8 = 0;
    while (slot < slot_count) : (slot += 1) {
        const source = if (descriptor.form_profile != 0)
            try vectorSlotSourceFromFormProfile(block, descriptor.form_profile, slot)
        else
            VectorSlotSource{ .block = block, .slot = slot };
        layout.slots[slot] = .{ .block = source.block, .slot = source.slot };
    }
    return layout;
}

fn descriptorTensorOnlySlotCount(descriptor: OrthogonalTensorDescriptor) !u8 {
    if (descriptor.has_spinor) return error.UnsupportedTensorBridge;
    return switch (descriptor.kind) {
        .scalar => 0,
        .vector_young, .exterior_form, .mixed_tensor_form => descriptor.young_box_count,
        else => error.UnsupportedTensorBridge,
    };
}

fn tensorOnlyEndpointKind(descriptor: OrthogonalTensorDescriptor) !TensorOnlyEndpointKind {
    if (descriptor.form_duality != .none) {
        if (descriptor.kind != .exterior_form) return error.UnsupportedTensorBridge;
        return .hodge_form;
    }
    return switch (descriptor.kind) {
        .scalar => .scalar,
        .vector_young => .vector_young,
        .exterior_form => .exterior_form,
        .mixed_tensor_form => .mixed_tensor_form,
        else => error.UnsupportedTensorBridge,
    };
}

fn compileGeneralTensorOnlyBrauerProgram(channel: TensorOnlyChannel) !TensorOnlyProgram {
    var program: TensorOnlyProgram = .{ .channel = channel };
    errdefer program.deinit();
    try budgetTensorOnlyRawDiagramsBeforeEnumeration(channel);
    try budgetTensorOnlyEndpointProjectorsBeforeConstruction(channel);
    var raw_diagrams: TensorBrauerDiagramBuffer = .{};
    try enumerateRawBrauerDiagrams(channel, &raw_diagrams);
    try pruneTensorOnlyTraceKilledRawDiagrams(channel, &raw_diagrams);
    program.raw_diagram_count = raw_diagrams.count;
    program.raw_diagrams = raw_diagrams.diagrams;
    program.left_projector_index = try appendTensorOnlyEndpointProjector(&program, channel.left, channel.dimension);
    program.right_projector_index = try appendTensorOnlyEndpointProjector(&program, channel.right, channel.dimension);
    program.output_projector_index = try appendTensorOnlyEndpointProjector(&program, channel.output, channel.dimension);
    try budgetTensorOnlyEndpointActionsBeforeConstruction(&program);
    try buildTensorOnlyEndpointActions(&program);
    try budgetTensorOnlyEndpointActionsBeforeGram(&program);
    try enumerateTensorOnlyCandidates(&program);
    if (program.candidate_count == 0) return error.UnsupportedStructuralProjectorTerm;
    try finishTensorOnlyProgram(&program);
    if (program.term_count == 0) return error.UnsupportedStructuralProjectorTerm;
    return program;
}

fn budgetTensorOnlyRawDiagramsBeforeEnumeration(channel: TensorOnlyChannel) !void {
    const total = channel.input_slot_count + channel.output_slot_count;
    if ((total & 1) != 0) return error.UnsupportedStructuralProjectorTerm;
    var estimated: u32 = 1;
    var factor: u32 = if (total == 0) 1 else total - 1;
    while (factor > 1) : (factor -= 2) {
        estimated = std.math.mul(u32, estimated, factor) catch return error.ProjectorProgramTooLarge;
        if (estimated > max_tensor_raw_diagrams) return error.ProjectorProgramTooLarge;
    }
}

fn budgetTensorOnlyEndpointProjectorsBeforeConstruction(channel: TensorOnlyChannel) !void {
    try budgetTensorOnlyEndpointProjectorBeforeConstruction(channel.left, channel.dimension);
    try budgetTensorOnlyEndpointProjectorBeforeConstruction(channel.right, channel.dimension);
    try budgetTensorOnlyEndpointProjectorBeforeConstruction(channel.output, channel.dimension);
}

fn budgetTensorOnlyEndpointProjectorBeforeConstruction(endpoint: TensorOnlyEndpoint, dimension: u16) !void {
    if (endpoint.slot_count == 0) return;
    if (endpoint.slot_count > max_tensor_slots) return error.UnsupportedTensorShapeOverCap;
    if (endpoint.duality != .none and @as(u16, endpoint.slot_count) * 2 != dimension) return error.UnsupportedTensorBridge;
    const shape = try tensorOnlyEndpointShape(endpoint);
    const factor = try tensorEndpointYoungTraceFreeFactor(shape);
    try budgetTensorEndpointProjectorFactorBeforeExpansion(factor);
}

fn compileTensorOnlyBrauerProgram(channel: TensorOnlyChannel) !TensorOnlyProgram {
    return compileGeneralTensorOnlyBrauerProgram(channel);
}

fn appendTensorOnlyEndpointProjector(program: *TensorOnlyProgram, endpoint: TensorOnlyEndpoint, dimension: u16) !u8 {
    const key = tensorOnlyEndpointProjectorKey(endpoint);
    var projector_index: u8 = 0;
    while (projector_index < program.projector_count) : (projector_index += 1) {
        if (tensorOnlyEndpointProjectorKeyEql(program.projector_keys[projector_index], key)) return projector_index;
    }
    if (program.projector_count == max_tensor_endpoint_projectors) return error.ProjectorProgramTooLarge;
    var projector = try endpointProjector(endpoint, dimension);
    errdefer projector.deinit();
    const out_index = program.projector_count;
    program.projector_keys[out_index] = key;
    program.projectors[out_index] = projector;
    program.projector_count += 1;
    return out_index;
}

fn tensorOnlyEndpointProjectorKey(endpoint: TensorOnlyEndpoint) TensorOnlyEndpointProjectorKey {
    return .{
        .kind = endpoint.kind,
        .slot_count = endpoint.slot_count,
        .row_count = endpoint.row_count,
        .rows = endpoint.rows,
        .hodge_duality = endpoint.duality,
    };
}

fn tensorOnlyEndpointProjectorKeyEql(left: TensorOnlyEndpointProjectorKey, right: TensorOnlyEndpointProjectorKey) bool {
    if (left.kind != right.kind or
        left.slot_count != right.slot_count or
        left.row_count != right.row_count or
        left.hodge_duality != right.hodge_duality) return false;
    var row_index: u8 = 0;
    while (row_index < max_young_rows) : (row_index += 1) {
        if (left.rows[row_index] != right.rows[row_index]) return false;
    }
    return true;
}

fn pruneTensorOnlyTraceKilledRawDiagrams(channel: TensorOnlyChannel, diagrams: *TensorBrauerDiagramBuffer) !void {
    var out: TensorBrauerDiagramBuffer = .{};
    var diagram_index: u8 = 0;
    while (diagram_index < diagrams.count) : (diagram_index += 1) {
        const diagram = diagrams.diagrams[diagram_index];
        if (tensorOnlyRawDiagramSurvivesEndpointTraceFree(channel, diagram)) try out.append(diagram);
    }
    if (out.count == 0) return error.UnsupportedStructuralProjectorTerm;
    diagrams.* = out;
}

fn tensorOnlyRawDiagramSurvivesEndpointTraceFree(channel: TensorOnlyChannel, diagram: TensorBrauerDiagram) bool {
    var edge_index: u8 = 0;
    while (edge_index < diagram.edge_count) : (edge_index += 1) {
        const edge = diagram.edges[edge_index];
        switch (edge.kind) {
            .delta => {},
            .output_metric => if (tensorOnlyEndpointTraceFree(channel.output)) return false,
            .input_trace => {
                const left_side = tensorOnlyInputSlotEndpointSide(channel, edge.input_a) orelse return false;
                const right_side = tensorOnlyInputSlotEndpointSide(channel, edge.input_b) orelse return false;
                if (left_side == right_side and tensorOnlyInputEndpointTraceFree(channel, left_side)) return false;
            },
        }
    }
    return true;
}

fn tensorOnlyInputSlotEndpointSide(channel: TensorOnlyChannel, input_slot: u8) ?TensorEndpointSide {
    if (input_slot < channel.left.slot_count) return .left;
    if (input_slot < channel.input_slot_count) return .right;
    return null;
}

fn tensorOnlyInputEndpointTraceFree(channel: TensorOnlyChannel, side: TensorEndpointSide) bool {
    return switch (side) {
        .left => tensorOnlyEndpointTraceFree(channel.left),
        .right => tensorOnlyEndpointTraceFree(channel.right),
        .output => false,
    };
}

fn tensorOnlyEndpointTraceFree(endpoint: TensorOnlyEndpoint) bool {
    return endpoint.slot_count != 0;
}

fn endpointProjector(endpoint: TensorOnlyEndpoint, dimension: u16) !EndpointProjector {
    if (endpoint.slot_count == 0) return .{};
    if (endpoint.slot_count > max_tensor_slots) return error.UnsupportedTensorShapeOverCap;
    if (endpoint.duality != .none and @as(u16, endpoint.slot_count) * 2 != dimension) return error.UnsupportedTensorBridge;
    const shape = try tensorOnlyEndpointShape(endpoint);
    var young_factor = try tensorEndpointYoungTraceFreeFactor(shape);
    try budgetTensorEndpointProjectorFactorBeforeExpansion(young_factor);

    var projector = EndpointProjector{
        .is_identity = false,
        .hodge_duality = endpoint.duality,
    };
    try appendTensorEndpointYoungPermutationOperators(&projector, shape);
    if (young_factor.trace_generator_count != 0) {
        var young_candidates: BrauerCandidateBuffer = .{};
        try appendVectorYoungPermutationCandidates(shape, endpoint.slot_count, &young_candidates);
        try uniqueBrauerWords(&young_candidates);
        if (young_candidates.count != 1) return error.UnsupportedStructuralProjectorTerm;

        try appendTensorEndpointYoungNormalizationOperator(&projector, shape, endpoint.slot_count, dimension, young_candidates.candidates[0]);
        try appendTensorEndpointTraceRemovalProgramFromShape(&projector, shape, dimension, young_candidates.candidates[0], &young_factor);
    }
    if (endpoint.duality != .none) {
        projector.operators[projector.operator_count] = .{ .kind = .hodge_projector };
        projector.operator_count += 1;
    }
    if (projector.operator_count == 0 and endpoint.duality == .none) return .{};
    return projector;
}

fn traceFreeProjectorIsIdentity(projector: TraceFreeBrauerProjector, rank: u8) !bool {
    if (projector.basis_count != 1) return false;
    if (!rationalValueEql(projector.coefficients[0], Rational.one())) return false;
    const candidate = projector.basis[0];
    if (candidate.word_count != 1) return false;
    var word = candidate.words[0];
    if (!rationalValueEql(word.coefficient, Rational.one())) return false;
    word.coefficient = Rational.one();
    const identity = try identityBrauerWord(rank);
    return brauerWordEdgesEql(word, identity);
}

fn tensorEndpointYoungTraceFreeFactor(shape: YoungShape) !TensorEndpointOperatorFactor {
    return .{
        .kind = .young_trace_free_projector,
        .row_factor_count = shape.row_count,
        .column_factor_count = shape.rows[0],
        .trace_generator_count = tensorEndpointTraceGeneratorCount(shape),
        .young_word_upper_bound = try tensorEndpointYoungWordUpperBound(shape),
    };
}

fn budgetTensorEndpointProjectorFactorBeforeExpansion(factor: TensorEndpointOperatorFactor) !void {
    if (factor.young_word_upper_bound > max_young_permutation_terms) return error.ProjectorProgramTooLarge;
    if (factor.trace_generator_count >= max_vector_brauer_candidates) return error.ProjectorProgramTooLarge;
}

fn appendTensorEndpointYoungPermutationOperators(projector: *EndpointProjector, shape: YoungShape) !void {
    var row_start: u8 = 0;
    var row_index: u8 = 0;
    while (row_index < shape.row_count) : (row_index += 1) {
        const row_len = shape.rows[row_index];
        var slots = [_]u8{0} ** max_tensor_slots;
        var slot: u8 = 0;
        while (slot < row_len) : (slot += 1) {
            slots[slot] = row_start + slot;
        }
        try appendTensorEndpointYoungPermutationOperator(projector, .young_row_symmetrizer, slots, row_len);
        row_start += row_len;
    }

    var column: u8 = 0;
    while (column < shape.rows[0]) : (column += 1) {
        var slots = [_]u8{0} ** max_tensor_slots;
        var count: u8 = 0;
        row_start = 0;
        row_index = 0;
        while (row_index < shape.row_count) : (row_index += 1) {
            const row_len = shape.rows[row_index];
            if (column < row_len) {
                slots[count] = row_start + column;
                count += 1;
            }
            row_start += row_len;
        }
        try appendTensorEndpointYoungPermutationOperator(projector, .young_column_antisymmetrizer, slots, count);
    }
}

fn appendTensorEndpointYoungPermutationOperator(projector: *EndpointProjector, kind: TensorEndpointOperatorKind, slots: [max_tensor_slots]u8, slot_count: u8) !void {
    if (slot_count <= 1) return;
    if (projector.operator_count == max_tensor_word_factors) return error.ProjectorProgramTooLarge;
    projector.operators[projector.operator_count] = .{
        .kind = kind,
        .slot_count = slot_count,
        .slots = slots,
    };
    projector.operator_count += 1;
}

fn appendTensorEndpointSingleTraceRemovalOperator(projector: *EndpointProjector, trace_slot_a: u8, trace_slot_b: u8, coefficient: Rational, factor: TensorEndpointOperatorFactor) !void {
    if (coefficient.numerator == 0) return;
    if (projector.operator_count == max_tensor_word_factors) return error.ProjectorProgramTooLarge;
    if (projector.trace_branch_count == max_tensor_trace_removal_branches) return error.ProjectorProgramTooLarge;
    projector.trace_branches[projector.trace_branch_count] = .{
        .coefficient = coefficient,
        .trace_count = 1,
        .trace_slot_a = traceSlotArray(trace_slot_a),
        .trace_slot_b = traceSlotArray(trace_slot_b),
    };
    const branch_first = projector.trace_branch_count;
    projector.trace_branch_count += 1;
    projector.operators[projector.operator_count] = .{
        .kind = .trace_removal_projector,
        .trace_generator_count = factor.trace_generator_count,
        .trace_basis_count = factor.trace_basis_count,
        .trace_branch_first = branch_first,
        .trace_branch_count = 1,
    };
    projector.operator_count += 1;
}

fn appendTensorEndpointYoungNormalizationOperator(projector: *EndpointProjector, shape: YoungShape, rank: u8, dimension: u16, young_candidate: BrauerCandidate) !void {
    const coefficient = try tensorEndpointYoungNormalizationCoefficient(shape, rank, dimension, young_candidate);
    try appendTensorEndpointScalarOperator(projector, coefficient);
}

fn tensorEndpointYoungNormalizationCoefficient(shape: YoungShape, rank: u8, dimension: u16, young_candidate: BrauerCandidate) !Rational {
    const group_size = try tensorEndpointYoungWordUpperBound(shape);
    const square = try composeBrauerCandidates(rank, dimension, young_candidate, young_candidate);
    const scale = try brauerCandidateProportionalScale(young_candidate, square);
    return try (try Rational.init(group_size, 1)).div(scale);
}

fn appendTensorEndpointScalarOperator(projector: *EndpointProjector, coefficient: Rational) !void {
    if (rationalValueEql(coefficient, Rational.one())) return;
    if (projector.operator_count == max_tensor_word_factors) return error.ProjectorProgramTooLarge;
    projector.operators[projector.operator_count] = .{
        .kind = .scalar_multiplier,
        .scalar_coefficient = coefficient,
    };
    projector.operator_count += 1;
}

fn appendTensorEndpointTraceRemovalProgram(projector: *EndpointProjector, trace_free: TraceFreeBrauerProjector, shape: YoungShape, factor: TensorEndpointOperatorFactor) !bool {
    if (trace_free.basis_count <= 1) return false;
    if (projector.operator_count == max_tensor_word_factors) return error.ProjectorProgramTooLarge;
    const first_branch = projector.trace_branch_count;
    var basis_index: u8 = 1;
    while (basis_index < trace_free.basis_count) : (basis_index += 1) {
        const coefficient = trace_free.coefficients[basis_index];
        if (coefficient.numerator == 0) continue;
        const path = trace_free.paths[basis_index];
        if (path.trace_count == 0) return false;
        if (projector.trace_branch_count == max_tensor_trace_removal_branches) return error.ProjectorProgramTooLarge;
        var branch = TensorTraceRemovalBranch{
            .coefficient = coefficient,
            .trace_count = path.trace_count,
        };
        var step: u8 = 0;
        while (step < path.trace_count) : (step += 1) {
            const pair = tensorEndpointTracePairAt(shape, path.trace_indices[step]) orelse return false;
            branch.trace_slot_a[step] = pair[0];
            branch.trace_slot_b[step] = pair[1];
        }
        projector.trace_branches[projector.trace_branch_count] = branch;
        projector.trace_branch_count += 1;
    }
    const branch_count = projector.trace_branch_count - first_branch;
    if (branch_count == 0) return false;
    projector.operators[projector.operator_count] = .{
        .kind = .trace_removal_projector,
        .trace_generator_count = factor.trace_generator_count,
        .trace_basis_count = factor.trace_basis_count,
        .trace_branch_first = first_branch,
        .trace_branch_count = branch_count,
    };
    projector.operator_count += 1;
    return true;
}

fn appendTensorEndpointTraceRemovalProgramFromShape(projector: *EndpointProjector, shape: YoungShape, dimension: u16, young_candidate: BrauerCandidate, factor: *TensorEndpointOperatorFactor) !void {
    var trace_generators: BrauerCandidateBuffer = .{};
    try appendVectorYoungTraceCandidatesForShape(shape, &trace_generators);
    if (trace_generators.count == 0) return;

    const young_idempotent = try normalizedBrauerIdempotentCandidate(shape.box_count, dimension, young_candidate);
    var basis: BrauerCandidateBuffer = .{};
    var paths: TraceRemovalPathBuffer = .{};
    try buildTraceClosureBasis(shape.box_count, dimension, young_idempotent, &trace_generators, &basis, &paths);
    if (basis.count == 0) return error.UnsupportedStructuralProjectorTerm;
    if (paths.count != basis.count) return error.UnsupportedStructuralProjectorTerm;
    factor.trace_basis_count = basis.count;
    if (basis.count == 1) return;

    const solution = try solveTraceRemovalCoefficients(shape.box_count, dimension, &basis, &trace_generators);
    try appendTensorEndpointTraceRemovalBranches(projector, shape, paths, solution, factor.*);
}

fn appendTensorEndpointTraceRemovalBranches(projector: *EndpointProjector, shape: YoungShape, paths: TraceRemovalPathBuffer, coefficients: [max_vector_brauer_candidates]Rational, factor: TensorEndpointOperatorFactor) !void {
    if (projector.operator_count == max_tensor_word_factors) return error.ProjectorProgramTooLarge;
    const first_branch = projector.trace_branch_count;
    var basis_index: u8 = 1;
    while (basis_index < paths.count) : (basis_index += 1) {
        const coefficient = coefficients[basis_index - 1];
        if (coefficient.numerator == 0) continue;
        const path = paths.paths[basis_index];
        if (path.trace_count == 0) return error.UnsupportedStructuralProjectorTerm;
        if (projector.trace_branch_count == max_tensor_trace_removal_branches) return error.ProjectorProgramTooLarge;
        var branch = TensorTraceRemovalBranch{
            .coefficient = coefficient,
            .trace_count = path.trace_count,
        };
        var step: u8 = 0;
        while (step < path.trace_count) : (step += 1) {
            const pair = tensorEndpointTracePairAt(shape, path.trace_indices[step]) orelse return error.UnsupportedStructuralProjectorTerm;
            branch.trace_slot_a[step] = pair[0];
            branch.trace_slot_b[step] = pair[1];
        }
        projector.trace_branches[projector.trace_branch_count] = branch;
        projector.trace_branch_count += 1;
    }
    const branch_count = projector.trace_branch_count - first_branch;
    if (branch_count == 0) return;
    projector.operators[projector.operator_count] = .{
        .kind = .trace_removal_projector,
        .trace_generator_count = factor.trace_generator_count,
        .trace_basis_count = factor.trace_basis_count,
        .trace_branch_first = first_branch,
        .trace_branch_count = branch_count,
    };
    projector.operator_count += 1;
}

fn traceSlotArray(slot: u8) [max_tensor_trace_path_steps]u8 {
    var out = [_]u8{0} ** max_tensor_trace_path_steps;
    out[0] = slot;
    return out;
}

fn tensorEndpointTracePairAt(shape: YoungShape, target_index: u8) ?[2]u8 {
    var trace_index: u8 = 0;
    var left: u8 = 0;
    while (left < shape.box_count) : (left += 1) {
        var right = left + 1;
        while (right < shape.box_count) : (right += 1) {
            if (!youngTracePairAdmissible(shape, left, right)) continue;
            if (trace_index == target_index) return .{ left, right };
            trace_index += 1;
        }
    }
    return null;
}

fn tensorEndpointYoungWordUpperBound(shape: YoungShape) !u16 {
    var count: u32 = 1;
    var row: u8 = 0;
    while (row < shape.row_count) : (row += 1) {
        count = try checkedMulU32(count, try factorialU32(shape.rows[row]));
        if (count > max_young_permutation_terms) return max_young_permutation_terms + 1;
    }
    var column: u8 = 0;
    while (column < shape.rows[0]) : (column += 1) {
        count = try checkedMulU32(count, try factorialU32(youngColumnHeight(shape, column)));
        if (count > max_young_permutation_terms) return max_young_permutation_terms + 1;
    }
    return @intCast(count);
}

fn factorialU32(value: u8) !u32 {
    var out: u32 = 1;
    var factor: u8 = 2;
    while (factor <= value) : (factor += 1) {
        out = try checkedMulU32(out, factor);
    }
    return out;
}

fn tensorEndpointTraceGeneratorCount(shape: YoungShape) u8 {
    var count: u8 = 0;
    var left: u8 = 0;
    while (left < shape.box_count) : (left += 1) {
        var right = left + 1;
        while (right < shape.box_count) : (right += 1) {
            if (youngTracePairAdmissible(shape, left, right)) count += 1;
        }
    }
    return count;
}

fn youngColumnHeight(shape: YoungShape, column: u8) u8 {
    var height: u8 = 0;
    var row: u8 = 0;
    while (row < shape.row_count) : (row += 1) {
        if (shape.rows[row] > column) height += 1;
    }
    return height;
}

fn tensorOnlyEndpointShape(endpoint: TensorOnlyEndpoint) !YoungShape {
    if (endpoint.slot_count == 0) return .{};
    if (endpoint.row_count == 0) return error.UnsupportedStructuralProjectorTerm;
    const shape: YoungShape = .{
        .row_count = endpoint.row_count,
        .rows = endpoint.rows,
        .box_count = endpoint.slot_count,
    };
    if ((try youngBoxCount(shape.row_count, shape.rows)) != shape.box_count) return error.InvalidYoungShape;
    return shape;
}

fn enumerateTensorOnlyCandidates(program: *TensorOnlyProgram) !void {
    const left_projector = tensorOnlyProgramLeftProjector(program);
    const right_projector = tensorOnlyProgramRightProjector(program);
    const output_projector = tensorOnlyProgramOutputProjector(program);
    var raw_index: u8 = 0;
    while (raw_index < program.raw_diagram_count) : (raw_index += 1) {
        var word: TensorOnlyCandidateWord = .{};
        if (!left_projector.is_identity) try word.append(.{ .kind = .left_projector, .candidate_index = 0 });
        if (!right_projector.is_identity) try word.append(.{ .kind = .right_projector, .candidate_index = 0 });
        try word.append(.{ .kind = .raw_brauer_diagram, .candidate_index = raw_index });
        if (!output_projector.is_identity) try word.append(.{ .kind = .output_projector, .candidate_index = 0 });
        if (left_projector.hodge_duality != .none) try word.append(.{ .kind = .hodge_projector, .candidate_index = 0 });
        if (right_projector.hodge_duality != .none) try word.append(.{ .kind = .hodge_projector, .candidate_index = 1 });
        if (output_projector.hodge_duality != .none) try word.append(.{ .kind = .hodge_projector, .candidate_index = 2 });
        try appendTensorOnlyCandidate(program, word);
    }
}

fn appendTensorOnlyCandidate(program: *TensorOnlyProgram, word: TensorOnlyCandidateWord) !void {
    if (program.candidate_count == max_tensor_candidates) return error.UnsupportedTensorBrauerCandidateCap;
    program.candidates[program.candidate_count] = word;
    program.candidate_count += 1;
}

fn buildTensorOnlyEndpointActions(program: *TensorOnlyProgram) !void {
    var raw_index: u8 = 0;
    while (raw_index < program.raw_diagram_count) : (raw_index += 1) {
        var raw_action: TensorEndpointActionBuildBuffer = .{};
        try appendTensorEndpointActionWord(&raw_action, .{ .word = program.raw_diagrams[raw_index] });
        const left_action = try appendTensorEndpointAction(
            program,
            program.left_projector_index,
            .left,
            raw_index,
            raw_action,
        );
        const right_action = try appendTensorEndpointAction(
            program,
            program.right_projector_index,
            .right,
            raw_index,
            tensorEndpointBuildBufferFromAction(program.endpoint_actions[left_action]),
        );
        const output_action = try appendTensorEndpointAction(
            program,
            program.output_projector_index,
            .output,
            raw_index,
            tensorEndpointBuildBufferFromAction(program.endpoint_actions[right_action]),
        );
        program.projected_raw_action_indices[raw_index] = output_action;
    }
}

fn appendTensorEndpointAction(program: *TensorOnlyProgram, projector_index: u8, side: TensorEndpointSide, raw_index: u8, input: TensorEndpointActionBuildBuffer) !u16 {
    const key: TensorEndpointActionKey = .{
        .endpoint_projector_index = projector_index,
        .side = side,
        .raw_diagram_index = raw_index,
        .input_word_count = input.word_count,
        .boundary_signature = tensorEndpointActionBoundarySignature(program.channel, input),
    };
    if (findTensorEndpointAction(program, key)) |action_index| return action_index;
    if (program.endpoint_action_count == max_tensor_endpoint_actions) return error.ProjectorProgramTooLarge;
    const projector = &program.projectors[projector_index];
    const action = applyTensorEndpointProjectorAction(program.channel, side, projector, input) catch |err| switch (err) {
        error.UnsupportedTensorBrauerCandidateCap => return error.ProjectorProgramTooLarge,
        else => return err,
    };
    if (action.word_count > max_tensor_endpoint_action_words) return error.ProjectorProgramTooLarge;

    const allocator = std.heap.page_allocator;
    const words = try allocator.alloc(TensorEndpointActionWord, action.word_count);
    errdefer allocator.free(words);
    @memcpy(words[0..action.word_count], action.words[0..action.word_count]);

    const action_index = program.endpoint_action_count;
    program.endpoint_actions[action_index] = .{
        .key = key,
        .word_count = action.word_count,
        .words = words,
    };
    program.endpoint_action_count += 1;
    return action_index;
}

fn findTensorEndpointAction(program: *const TensorOnlyProgram, key: TensorEndpointActionKey) ?u16 {
    var action_index: u16 = 0;
    while (action_index < program.endpoint_action_count) : (action_index += 1) {
        if (tensorEndpointActionKeyEql(program.endpoint_actions[action_index].key, key)) return action_index;
    }
    return null;
}

fn tensorEndpointActionKeyEql(left: TensorEndpointActionKey, right: TensorEndpointActionKey) bool {
    return left.endpoint_projector_index == right.endpoint_projector_index and
        left.side == right.side and
        left.raw_diagram_index == right.raw_diagram_index and
        left.input_word_count == right.input_word_count and
        left.boundary_signature == right.boundary_signature;
}

fn applyTensorEndpointProjectorAction(channel: TensorOnlyChannel, side: TensorEndpointSide, projector: *const EndpointProjector, input: TensorEndpointActionBuildBuffer) !TensorEndpointActionBuildBuffer {
    var current = input;
    var operator_index: u8 = 0;
    while (operator_index < projector.operator_count) : (operator_index += 1) {
        current = switch (projector.operators[operator_index].kind) {
            .young_row_symmetrizer, .young_column_antisymmetrizer => try applyTensorYoungPermutationEndpointOperator(channel, side, projector.operators[operator_index], current),
            .scalar_multiplier => try applyTensorScalarEndpointOperator(projector.operators[operator_index], current),
            .trace_removal_projector => try applyTensorTraceRemovalEndpointOperator(channel, side, projector, projector.operators[operator_index], current),
            .young_trace_free_projector => blk: {
                if (!projector.diagnostic_trace_free_basis) return error.UnsupportedStructuralProjectorTerm;
                break :blk try applyTensorYoungTraceFreeEndpointOperator(channel, side, projector, current);
            },
            .hodge_projector => try applyTensorHodgeEndpointOperator(channel, side, projector, current),
        };
    }
    return current;
}

fn applyTensorYoungPermutationEndpointOperator(channel: TensorOnlyChannel, side: TensorEndpointSide, operator: TensorEndpointOperatorFactor, input: TensorEndpointActionBuildBuffer) !TensorEndpointActionBuildBuffer {
    const rank = tensorEndpointActionRank(channel, side);
    const antisymmetric = operator.kind == .young_column_antisymmetrizer;
    const group = try youngGroupPermutationSum(operator.slots, operator.slot_count, rank, antisymmetric);
    const normalization = try Rational.init(1, try factorialI64(operator.slot_count));

    var out: TensorEndpointActionBuildBuffer = .{};
    var input_word_index: u8 = 0;
    while (input_word_index < input.word_count) : (input_word_index += 1) {
        var term_index: u8 = 0;
        while (term_index < group.count) : (term_index += 1) {
            const term = group.terms[term_index];
            if (term.coefficient.numerator == 0) continue;
            const projector_word = try tensorEndpointPermutationOperatorWord(rank, term, normalization);
            var action_word = input.words[input_word_index];
            action_word.word = try applyTensorEndpointProjectorWord(channel, side, projector_word, input.words[input_word_index].word);
            try appendMergedTensorEndpointActionWord(&out, action_word);
        }
    }
    return out;
}

fn tensorEndpointPermutationOperatorWord(rank: u8, term: YoungPermutationTerm, normalization: Rational) !BrauerWord {
    var word: BrauerWord = .{ .coefficient = try term.coefficient.mul(normalization) };
    var slot: u8 = 0;
    while (slot < rank) : (slot += 1) {
        try appendBrauerDeltaEdge(&word, slot, term.permutation[slot]);
    }
    canonicalizeBrauerWord(&word);
    return word;
}

fn applyTensorScalarEndpointOperator(operator: TensorEndpointOperatorFactor, input: TensorEndpointActionBuildBuffer) !TensorEndpointActionBuildBuffer {
    var out: TensorEndpointActionBuildBuffer = .{};
    var input_word_index: u8 = 0;
    while (input_word_index < input.word_count) : (input_word_index += 1) {
        var action_word = input.words[input_word_index];
        action_word.word.coefficient = try action_word.word.coefficient.mul(operator.scalar_coefficient);
        try appendMergedTensorEndpointActionWord(&out, action_word);
    }
    return out;
}

fn applyTensorTraceRemovalEndpointOperator(channel: TensorOnlyChannel, side: TensorEndpointSide, projector: *const EndpointProjector, operator: TensorEndpointOperatorFactor, input: TensorEndpointActionBuildBuffer) !TensorEndpointActionBuildBuffer {
    const rank = tensorEndpointActionRank(channel, side);
    var out: TensorEndpointActionBuildBuffer = .{};
    var input_word_index: u8 = 0;
    while (input_word_index < input.word_count) : (input_word_index += 1) {
        try appendMergedTensorEndpointActionWord(&out, input.words[input_word_index]);
        var branch_index: u8 = 0;
        while (branch_index < operator.trace_branch_count) : (branch_index += 1) {
            const branch = projector.trace_branches[operator.trace_branch_first + branch_index];
            if (branch.coefficient.numerator == 0) continue;
            var action_word = input.words[input_word_index];
            var step: u8 = 0;
            while (step < branch.trace_count) : (step += 1) {
                const trace_word = try tensorEndpointTraceOperatorWord(rank, branch.trace_slot_a[step], branch.trace_slot_b[step], Rational.one());
                action_word.word = try applyTensorEndpointProjectorWord(channel, side, trace_word, action_word.word);
            }
            action_word.word.coefficient = try action_word.word.coefficient.mul(branch.coefficient);
            try appendMergedTensorEndpointActionWord(&out, action_word);
        }
    }
    return out;
}

fn tensorEndpointTraceOperatorWord(rank: u8, left: u8, right: u8, coefficient: Rational) !BrauerWord {
    if (left >= rank or right >= rank or left == right) return error.UnsupportedStructuralProjectorTerm;
    var word: BrauerWord = .{ .coefficient = coefficient };
    try appendBrauerInputTraceEdge(&word, left, right);
    try appendBrauerOutputMetricEdge(&word, left, right);
    var slot: u8 = 0;
    while (slot < rank) : (slot += 1) {
        if (slot != left and slot != right) try appendBrauerDeltaEdge(&word, slot, slot);
    }
    canonicalizeBrauerWord(&word);
    return word;
}

fn applyTensorYoungTraceFreeEndpointOperator(channel: TensorOnlyChannel, side: TensorEndpointSide, projector: *const EndpointProjector, input: TensorEndpointActionBuildBuffer) !TensorEndpointActionBuildBuffer {
    var out: TensorEndpointActionBuildBuffer = .{};
    var input_word_index: u8 = 0;
    while (input_word_index < input.word_count) : (input_word_index += 1) {
        var basis_index: u8 = 0;
        while (basis_index < endpointProjectorBasisCount(projector)) : (basis_index += 1) {
            var projector_word_index: u8 = 0;
            while (projector_word_index < endpointProjectorWordCount(projector, basis_index)) : (projector_word_index += 1) {
                const rank = tensorEndpointActionRank(channel, side);
                const projector_word = try endpointProjectorWord(projector, rank, basis_index, projector_word_index);
                var action_word = input.words[input_word_index];
                action_word.word = try applyTensorEndpointProjectorWord(channel, side, projector_word, input.words[input_word_index].word);
                try appendMergedTensorEndpointActionWord(&out, action_word);
            }
        }
    }
    return out;
}

fn applyTensorHodgeEndpointOperator(channel: TensorOnlyChannel, side: TensorEndpointSide, projector: *const EndpointProjector, input: TensorEndpointActionBuildBuffer) !TensorEndpointActionBuildBuffer {
    if (projector.hodge_duality == .none) return input;
    const endpoint = tensorOnlyEndpointForSide(channel, side);
    const hodge: TensorEndpointHodgeAction = .{
        .side = side,
        .block = endpoint.block,
        .duality = projector.hodge_duality,
    };
    const signed_numerator: i64 = switch (projector.hodge_duality) {
        .self_dual => 1,
        .anti_self_dual => -1,
        .none => 0,
    };
    const half = try Rational.init(1, 2);
    const signed_half = try Rational.init(signed_numerator, 2);

    var out: TensorEndpointActionBuildBuffer = .{};
    var input_word_index: u8 = 0;
    while (input_word_index < input.word_count) : (input_word_index += 1) {
        var identity = input.words[input_word_index];
        identity.word.coefficient = try identity.word.coefficient.mul(half);
        try appendMergedTensorEndpointActionWord(&out, identity);

        var star = input.words[input_word_index];
        star.word.coefficient = try star.word.coefficient.mul(signed_half);
        try appendTensorEndpointActionWordHodge(&star, hodge);
        try appendMergedTensorEndpointActionWord(&out, star);
    }
    return out;
}

fn applyTensorEndpointProjectorWord(channel: TensorOnlyChannel, side: TensorEndpointSide, projector_word: BrauerWord, input_word: BrauerWord) !BrauerWord {
    return switch (side) {
        .left, .right => blk: {
            const input_projector = try remapTensorOnlyInputEndpointProjectorWord(channel, side, projector_word);
            break :blk try composeRectangularBrauerWords(
                channel.input_slot_count,
                channel.input_slot_count,
                channel.output_slot_count,
                channel.dimension,
                input_word,
                input_projector,
            );
        },
        .output => try composeRectangularBrauerWords(
            channel.input_slot_count,
            channel.output_slot_count,
            channel.output_slot_count,
            channel.dimension,
            projector_word,
            input_word,
        ),
    };
}

fn remapTensorOnlyInputEndpointProjectorWord(channel: TensorOnlyChannel, side: TensorEndpointSide, projector_word: BrauerWord) !BrauerWord {
    var out: BrauerWord = .{ .coefficient = projector_word.coefficient };
    switch (side) {
        .left => {
            try appendRemappedSquareBrauerWord(&out, projector_word, 0);
            try appendTensorOnlyIdentitySquareSlots(&out, channel.left.slot_count, channel.right.slot_count);
        },
        .right => {
            try appendTensorOnlyIdentitySquareSlots(&out, 0, channel.left.slot_count);
            try appendRemappedSquareBrauerWord(&out, projector_word, channel.left.slot_count);
        },
        .output => return error.UnsupportedStructuralProjectorTerm,
    }
    if (out.edge_count != channel.input_slot_count) return error.UnsupportedStructuralProjectorTerm;
    canonicalizeBrauerWord(&out);
    return out;
}

fn appendTensorOnlyIdentitySquareSlots(out: *BrauerWord, start_slot: u8, count: u8) !void {
    var slot: u8 = 0;
    while (slot < count) : (slot += 1) {
        try appendBrauerDeltaEdge(out, start_slot + slot, start_slot + slot);
    }
}

fn tensorEndpointActionRank(channel: TensorOnlyChannel, side: TensorEndpointSide) u8 {
    return switch (side) {
        .left => channel.left.slot_count,
        .right => channel.right.slot_count,
        .output => channel.output.slot_count,
    };
}

fn tensorOnlyEndpointForSide(channel: TensorOnlyChannel, side: TensorEndpointSide) TensorOnlyEndpoint {
    return switch (side) {
        .left => channel.left,
        .right => channel.right,
        .output => channel.output,
    };
}

fn tensorEndpointBuildBufferFromAction(action: TensorEndpointActionBuffer) TensorEndpointActionBuildBuffer {
    var out: TensorEndpointActionBuildBuffer = .{};
    var word_index: u8 = 0;
    while (word_index < action.word_count) : (word_index += 1) {
        out.words[word_index] = action.words[word_index];
    }
    out.word_count = action.word_count;
    return out;
}

fn appendTensorEndpointActionWord(out: *TensorEndpointActionBuildBuffer, word: TensorEndpointActionWord) !void {
    if (out.word_count == max_tensor_endpoint_action_words) return error.UnsupportedTensorBrauerCandidateCap;
    out.words[out.word_count] = word;
    out.word_count += 1;
}

fn appendMergedTensorEndpointActionWord(out: *TensorEndpointActionBuildBuffer, word: TensorEndpointActionWord) !void {
    var existing: u8 = 0;
    while (existing < out.word_count) : (existing += 1) {
        if (!tensorEndpointActionWordEqlExceptCoefficient(out.words[existing], word)) continue;
        out.words[existing].word.coefficient = try out.words[existing].word.coefficient.add(word.word.coefficient);
        if (out.words[existing].word.coefficient.numerator == 0) {
            var shift = existing;
            while (shift + 1 < out.word_count) : (shift += 1) {
                out.words[shift] = out.words[shift + 1];
            }
            out.word_count -= 1;
        }
        return;
    }
    try appendTensorEndpointActionWord(out, word);
}

fn appendTensorEndpointActionWordHodge(word: *TensorEndpointActionWord, hodge: TensorEndpointHodgeAction) !void {
    if (word.hodge_count == max_tensor_endpoint_projectors) return error.UnsupportedTensorBrauerCandidateCap;
    word.hodge_actions[word.hodge_count] = hodge;
    word.hodge_count += 1;
}

fn tensorEndpointActionWordEqlExceptCoefficient(left: TensorEndpointActionWord, right: TensorEndpointActionWord) bool {
    return brauerWordEdgesEql(left.word, right.word) and tensorEndpointActionWordHodgeEql(left, right);
}

fn tensorEndpointActionWordHodgeEql(left: TensorEndpointActionWord, right: TensorEndpointActionWord) bool {
    if (left.hodge_count != right.hodge_count) return false;
    var hodge_index: u8 = 0;
    while (hodge_index < left.hodge_count) : (hodge_index += 1) {
        const left_hodge = left.hodge_actions[hodge_index];
        const right_hodge = right.hodge_actions[hodge_index];
        if (left_hodge.side != right_hodge.side or
            left_hodge.block != right_hodge.block or
            left_hodge.duality != right_hodge.duality) return false;
    }
    return true;
}

fn tensorEndpointActionBoundarySignature(channel: TensorOnlyChannel, input: TensorEndpointActionBuildBuffer) u64 {
    var signature: u64 = 0xcbf29ce484222325;
    hashMixU64(&signature, channel.dimension);
    hashMixU64(&signature, channel.input_slot_count);
    hashMixU64(&signature, channel.output_slot_count);
    hashMixU64(&signature, input.word_count);
    var word_index: u8 = 0;
    while (word_index < input.word_count) : (word_index += 1) {
        const word = input.words[word_index];
        hashMixI64(&signature, word.word.coefficient.numerator);
        hashMixI64(&signature, word.word.coefficient.denominator);
        hashMixU64(&signature, word.word.edge_count);
        var edge_index: u8 = 0;
        while (edge_index < word.word.edge_count) : (edge_index += 1) {
            const edge = word.word.edges[edge_index];
            hashMixU64(&signature, @intFromEnum(edge.kind));
            hashMixU64(&signature, edge.input_a);
            hashMixU64(&signature, edge.input_b);
            hashMixU64(&signature, edge.output_a);
            hashMixU64(&signature, edge.output_b);
        }
        hashMixU64(&signature, word.hodge_count);
        var hodge_index: u8 = 0;
        while (hodge_index < word.hodge_count) : (hodge_index += 1) {
            const hodge = word.hodge_actions[hodge_index];
            hashMixU64(&signature, @intFromEnum(hodge.side));
            hashMixU64(&signature, hodge.block);
            hashMixU64(&signature, @intFromEnum(hodge.duality));
        }
    }
    return if (signature == 0) 1 else signature;
}

fn budgetTensorOnlyEndpointActionsBeforeConstruction(program: *const TensorOnlyProgram) !void {
    if (program.raw_diagram_count == 0) return error.UnsupportedStructuralProjectorTerm;
    if (@as(u16, program.raw_diagram_count) * 3 > max_tensor_endpoint_actions) return error.ProjectorProgramTooLarge;

    var words_per_raw: u32 = 1;
    words_per_raw = try budgetTensorEndpointActionWordsAfterProjector(words_per_raw, tensorOnlyProgramLeftProjector(program));
    words_per_raw = try budgetTensorEndpointActionWordsAfterProjector(words_per_raw, tensorOnlyProgramRightProjector(program));
    words_per_raw = try budgetTensorEndpointActionWordsAfterProjector(words_per_raw, tensorOnlyProgramOutputProjector(program));

    const total_projected_words = std.math.mul(u32, @as(u32, program.raw_diagram_count), words_per_raw) catch return error.ProjectorProgramTooLarge;
    if (total_projected_words == 0) return error.UnsupportedStructuralProjectorTerm;
    const gram_pair_work = std.math.mul(u64, total_projected_words, total_projected_words) catch return error.ProjectorProgramTooLarge;
    if (gram_pair_work > max_tensor_gram_action_pair_work) return error.ProjectorProgramTooLarge;
}

fn budgetTensorEndpointActionWordsAfterProjector(input_word_count: u32, projector: *const EndpointProjector) !u32 {
    var word_count = input_word_count;
    var operator_index: u8 = 0;
    while (operator_index < projector.operator_count) : (operator_index += 1) {
        const multiplier = try tensorEndpointOperatorActionWordMultiplier(projector.operators[operator_index]);
        word_count = std.math.mul(u32, word_count, multiplier) catch return error.ProjectorProgramTooLarge;
        if (word_count > max_tensor_endpoint_action_words) return error.ProjectorProgramTooLarge;
    }
    return word_count;
}

fn tensorEndpointOperatorActionWordMultiplier(operator: TensorEndpointOperatorFactor) !u32 {
    return switch (operator.kind) {
        .young_row_symmetrizer, .young_column_antisymmetrizer => factorialU32(operator.slot_count),
        .scalar_multiplier => 1,
        .trace_removal_projector => @as(u32, operator.trace_branch_count) + 1,
        .young_trace_free_projector => if (operator.trace_basis_count == 0) 1 else operator.trace_basis_count,
        .hodge_projector => 2,
    };
}

fn budgetTensorOnlyEndpointActionsBeforeGram(program: *const TensorOnlyProgram) !void {
    var total_projected_words: u64 = 0;
    var raw_index: u8 = 0;
    while (raw_index < program.raw_diagram_count) : (raw_index += 1) {
        const action = tensorOnlyProjectedRawAction(program, raw_index);
        total_projected_words += action.word_count;
    }
    if (total_projected_words == 0) return error.UnsupportedStructuralProjectorTerm;

    const gram_pair_work = total_projected_words * total_projected_words;
    if (gram_pair_work > max_tensor_gram_action_pair_work) return error.ProjectorProgramTooLarge;
}

fn finishTensorOnlyProgram(program: *TensorOnlyProgram) !void {
    const allocator = std.heap.page_allocator;
    const gram_width: usize = program.candidate_count;
    const gram = try allocator.alloc(Rational, gram_width * gram_width);
    defer allocator.free(gram);
    @memset(gram, Rational.zero());

    var row: usize = 0;
    while (row < program.candidate_count) : (row += 1) {
        var column: usize = 0;
        while (column <= row) : (column += 1) {
            const value = try tensorOnlyCandidateInnerProduct(program, program.candidates[row], program.candidates[column]);
            gram[row * gram_width + column] = value;
            gram[column * gram_width + row] = value;
        }
    }

    const pivots = try selectIndependentGramPivots(program.candidate_count, gram);
    if (pivots.count == 0) return error.SingularGramMatrix;
    if (pivots.count > max_tensor_pivots) return error.UnsupportedTensorPivotCap;

    var pivot_gram: [max_tensor_pivots * max_tensor_pivots]Rational = [_]Rational{Rational.zero()} ** (max_tensor_pivots * max_tensor_pivots);
    row = 0;
    while (row < pivots.count) : (row += 1) {
        var column: usize = 0;
        while (column < pivots.count) : (column += 1) {
            pivot_gram[row * pivots.count + column] = gram[@as(usize, pivots.pivots[row]) * gram_width + pivots.pivots[column]];
        }
    }

    program.pivot_count = pivots.count;
    var pivot_index: u8 = 0;
    while (pivot_index < pivots.count) : (pivot_index += 1) {
        program.pivots[pivot_index] = pivots.pivots[pivot_index];
    }
    program.inverse_gram = try invertSmallGram(pivots.count, pivot_gram[0..]);
    try budgetTensorOnlyPairTermsBeforeConstruction(program);
    program.term_count = try installTensorOnlyMergedPairTerms(program);
}

fn budgetTensorOnlyPairTermsBeforeConstruction(program: *const TensorOnlyProgram) !void {
    var total_action_pair_terms: u64 = 0;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
            if (coefficient.numerator == 0) continue;
            const action_count = try countTensorOnlyCandidatePairActionTerms(
                program,
                program.candidates[program.pivots[row]],
                program.candidates[program.pivots[column]],
                coefficient,
            );
            total_action_pair_terms += action_count;
            if (total_action_pair_terms > max_tensor_term_pair_work) return error.ProjectorProgramTooLarge;
        }
    }
}

fn installTensorOnlyMergedPairTerms(program: *TensorOnlyProgram) !u16 {
    const allocator = std.heap.page_allocator;
    var terms: std.ArrayList(VectorBrauerTerm) = .empty;
    errdefer terms.deinit(allocator);
    program.active_pair_term_count = 0;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const index = @as(usize, row) * max_tensor_pivots + column;
            if (terms.items.len > max_tensor_merged_terms) return error.ProjectorProgramTooLarge;
            program.pair_term_indices[index] = .{ .first_term = @intCast(terms.items.len), .term_count = 0 };
            const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
            if (coefficient.numerator == 0) continue;

            var pair_terms: std.ArrayList(VectorBrauerTerm) = .empty;
            defer pair_terms.deinit(allocator);
            try appendTensorOnlyCandidatePairMergedActionTerms(
                program,
                &pair_terms,
                program.candidates[program.pivots[row]],
                program.candidates[program.pivots[column]],
                coefficient,
            );
            if (pair_terms.items.len == 0) continue;
            if (pair_terms.items.len > max_tensor_merged_terms) return error.ProjectorProgramTooLarge;
            if (terms.items.len + pair_terms.items.len > max_tensor_merged_terms) return error.ProjectorProgramTooLarge;
            for (pair_terms.items) |term| {
                try terms.append(allocator, term);
            }
            program.pair_term_indices[index].term_count = @intCast(pair_terms.items.len);
            program.active_pair_term_indices[program.active_pair_term_count] = @intCast(index);
            program.active_pair_term_count += 1;
        }
    }
    program.merged_terms = try terms.toOwnedSlice(allocator);
    return @intCast(program.merged_terms.len);
}

fn tensorOnlyCandidateInnerProduct(program: *const TensorOnlyProgram, left: TensorOnlyCandidateWord, right: TensorOnlyCandidateWord) !Rational {
    const raw_left = try tensorOnlyWordRawDiagramIndex(program, left);
    const raw_right = try tensorOnlyWordRawDiagramIndex(program, right);
    return tensorEndpointActionInnerProduct(
        program.channel.dimension,
        program.channel.input_slot_count,
        program.channel.output_slot_count,
        tensorOnlyProjectedRawAction(program, raw_left),
        tensorOnlyProjectedRawAction(program, raw_right),
    );
}

fn tensorOnlyProjectedRawAction(program: *const TensorOnlyProgram, raw_index: u8) TensorEndpointActionBuffer {
    return program.endpoint_actions[program.projected_raw_action_indices[raw_index]];
}

fn tensorEndpointActionInnerProduct(dimension: u16, input_count: u8, output_count: u8, left: TensorEndpointActionBuffer, right: TensorEndpointActionBuffer) !Rational {
    var acc = Rational.zero();
    var left_index: u8 = 0;
    while (left_index < left.word_count) : (left_index += 1) {
        var right_index: u8 = 0;
        while (right_index < right.word_count) : (right_index += 1) {
            if (!tensorEndpointActionWordHodgeEql(left.words[left_index], right.words[right_index])) continue;
            acc = try acc.add(try tensorContractionWordInnerProduct(dimension, input_count, output_count, left.words[left_index].word, right.words[right_index].word));
        }
    }
    return acc;
}

fn tensorOnlyWordRawDiagramIndex(program: *const TensorOnlyProgram, word: TensorOnlyCandidateWord) !u8 {
    var found = false;
    var raw_index: u8 = 0;
    var factor_index: u8 = 0;
    while (factor_index < word.factor_count) : (factor_index += 1) {
        const factor = word.factors[factor_index];
        if (factor.kind != .raw_brauer_diagram) continue;
        if (found) return error.UnsupportedStructuralProjectorTerm;
        if (factor.candidate_index >= program.raw_diagram_count) return error.ProjectorConstructorTermOutOfBounds;
        found = true;
        raw_index = factor.candidate_index;
    }
    if (!found) return error.UnsupportedStructuralProjectorTerm;
    return raw_index;
}

fn tensorOnlyProgramLeftProjector(program: *const TensorOnlyProgram) *const EndpointProjector {
    return &program.projectors[program.left_projector_index];
}

fn tensorOnlyProgramRightProjector(program: *const TensorOnlyProgram) *const EndpointProjector {
    return &program.projectors[program.right_projector_index];
}

fn tensorOnlyProgramOutputProjector(program: *const TensorOnlyProgram) *const EndpointProjector {
    return &program.projectors[program.output_projector_index];
}

fn endpointProjectorBasisCount(projector: *const EndpointProjector) u8 {
    return if (projector.is_identity) 1 else projector.trace_free.basis_count;
}

fn endpointProjectorWordCount(projector: *const EndpointProjector, basis_index: u8) u8 {
    return if (projector.is_identity) 1 else projector.trace_free.basis[basis_index].word_count;
}

fn endpointProjectorWord(projector: *const EndpointProjector, rank: u8, basis_index: u8, word_index: u8) !BrauerWord {
    if (projector.is_identity) return identityBrauerWord(rank);
    if (basis_index >= projector.trace_free.basis_count) return error.ProjectorConstructorTermOutOfBounds;
    const basis = projector.trace_free.basis[basis_index];
    if (word_index >= basis.word_count) return error.ProjectorConstructorTermOutOfBounds;
    var word = basis.words[word_index];
    word.coefficient = try word.coefficient.mul(projector.trace_free.coefficients[basis_index]);
    return word;
}

fn identityBrauerWord(rank: u8) !BrauerWord {
    var word: BrauerWord = .{ .coefficient = Rational.one() };
    var slot: u8 = 0;
    while (slot < rank) : (slot += 1) {
        try appendBrauerDeltaEdge(&word, slot, slot);
    }
    return word;
}

fn appendRemappedSquareBrauerWord(out: *BrauerWord, word: BrauerWord, offset: u8) !void {
    var edge_index: u8 = 0;
    while (edge_index < word.edge_count) : (edge_index += 1) {
        const edge = word.edges[edge_index];
        switch (edge.kind) {
            .delta => try appendBrauerDeltaEdge(out, offset + edge.input_a, offset + edge.output_a),
            .input_trace => try appendBrauerInputTraceEdge(out, offset + edge.input_a, offset + edge.input_b),
            .output_metric => try appendBrauerOutputMetricEdge(out, offset + edge.output_a, offset + edge.output_b),
        }
    }
}

fn composeRectangularBrauerWords(input_count: u8, middle_count: u8, output_count: u8, dimension: u16, outer: BrauerWord, inner: BrauerWord) !BrauerWord {
    var graph: BrauerContraction = .{};
    const input_base: u8 = 0;
    const middle_base = input_count;
    const output_base = input_count + middle_count;
    const node_count = output_base + output_count;
    graph.initNodeCount(node_count);
    try graph.addRectangularWord(input_base, middle_base, inner);
    try graph.addRectangularWord(middle_base, output_base, outer);

    var out: BrauerWord = .{ .coefficient = try outer.coefficient.mul(inner.coefficient) };
    const loops = try appendRectangularCompositionEdges(&out, &graph, input_count, middle_count, output_count);
    out.coefficient = try out.coefficient.mul(try powRational(dimension, loops));
    canonicalizeBrauerWord(&out);
    return out;
}

fn appendRectangularCompositionEdges(word: *BrauerWord, graph: *BrauerContraction, input_count: u8, middle_count: u8, output_count: u8) !u8 {
    var loops: u8 = 0;
    const output_base = input_count + middle_count;
    const node_count = output_base + output_count;
    var root: u8 = 0;
    while (root < node_count) : (root += 1) {
        if (graph.find(root) != root) continue;
        var source_count: u8 = 0;
        var output_boundary_count: u8 = 0;
        var first_source: u8 = 0;
        var second_source: u8 = 0;
        var first_output: u8 = 0;
        var second_output: u8 = 0;

        var slot: u8 = 0;
        while (slot < input_count) : (slot += 1) {
            if (graph.find(slot) == root) {
                if (source_count == 0) first_source = slot else if (source_count == 1) second_source = slot;
                source_count += 1;
            }
        }
        slot = 0;
        while (slot < output_count) : (slot += 1) {
            if (graph.find(output_base + slot) == root) {
                if (output_boundary_count == 0) first_output = slot else if (output_boundary_count == 1) second_output = slot;
                output_boundary_count += 1;
            }
        }

        if (source_count == 0 and output_boundary_count == 0) {
            loops += 1;
        } else if (source_count == 1 and output_boundary_count == 1) {
            try appendBrauerDeltaEdge(word, first_source, first_output);
        } else if (source_count == 2 and output_boundary_count == 0) {
            try appendBrauerInputTraceEdge(word, first_source, second_source);
        } else if (source_count == 0 and output_boundary_count == 2) {
            try appendBrauerOutputMetricEdge(word, first_output, second_output);
        } else {
            return error.UnsupportedStructuralProjectorTerm;
        }
    }
    return loops;
}

fn countTensorOnlyProgramTerms(program: *const TensorOnlyProgram) !u16 {
    return program.term_count;
}

fn countTensorOnlyCandidatePairActionTerms(program: *const TensorOnlyProgram, left: TensorOnlyCandidateWord, right: TensorOnlyCandidateWord, coefficient: Rational) !u32 {
    if (coefficient.numerator == 0) return 0;
    const left_raw = try tensorOnlyWordRawDiagramIndex(program, left);
    const right_raw = try tensorOnlyWordRawDiagramIndex(program, right);
    const left_action = tensorOnlyProjectedRawAction(program, left_raw);
    const right_action = tensorOnlyProjectedRawAction(program, right_raw);
    var count: u32 = 0;
    var left_index: u8 = 0;
    while (left_index < left_action.word_count) : (left_index += 1) {
        var right_index: u8 = 0;
        while (right_index < right_action.word_count) : (right_index += 1) {
            const left_word = left_action.words[left_index];
            const right_word = right_action.words[right_index];
            if (!tensorEndpointActionWordHodgeEql(left_word, right_word)) continue;
            var word_coefficient = try coefficient.mul(left_word.word.coefficient);
            word_coefficient = try word_coefficient.mul(right_word.word.coefficient);
            if (word_coefficient.numerator == 0) continue;
            count += 1;
        }
    }
    return count;
}

fn appendTensorOnlyCandidatePairMergedActionTerms(program: *const TensorOnlyProgram, terms: *std.ArrayList(VectorBrauerTerm), left: TensorOnlyCandidateWord, right: TensorOnlyCandidateWord, coefficient: Rational) !void {
    if (coefficient.numerator == 0) return;
    const allocator = std.heap.page_allocator;
    const left_raw = try tensorOnlyWordRawDiagramIndex(program, left);
    const right_raw = try tensorOnlyWordRawDiagramIndex(program, right);
    const left_action = tensorOnlyProjectedRawAction(program, left_raw);
    const right_action = tensorOnlyProjectedRawAction(program, right_raw);
    var left_index: u8 = 0;
    while (left_index < left_action.word_count) : (left_index += 1) {
        var right_index: u8 = 0;
        while (right_index < right_action.word_count) : (right_index += 1) {
            const left_word = left_action.words[left_index];
            const right_word = right_action.words[right_index];
            if (!tensorEndpointActionWordHodgeEql(left_word, right_word)) continue;
            var word_coefficient = try coefficient.mul(left_word.word.coefficient);
            word_coefficient = try word_coefficient.mul(right_word.word.coefficient);
            if (word_coefficient.numerator == 0) continue;
            const term = try tensorOnlyActionWordPairTerm(program.channel, left_word, right_word, word_coefficient);
            try appendMergedTensorOnlyTerm(allocator, terms, term);
        }
    }
}

fn appendMergedTensorOnlyTerm(allocator: std.mem.Allocator, terms: *std.ArrayList(VectorBrauerTerm), term: VectorBrauerTerm) !void {
    if (term.coefficient.numerator == 0) return;
    var index: usize = 0;
    while (index < terms.items.len) : (index += 1) {
        if (!vectorBrauerTermAtomsEql(terms.items[index], term)) continue;
        terms.items[index].coefficient = try terms.items[index].coefficient.add(term.coefficient);
        if (terms.items[index].coefficient.numerator == 0) {
            var shift = index;
            while (shift + 1 < terms.items.len) : (shift += 1) {
                terms.items[shift] = terms.items[shift + 1];
            }
            terms.items.len -= 1;
        }
        return;
    }
    if (terms.items.len == max_tensor_merged_terms) return error.ProjectorProgramTooLarge;
    try terms.append(allocator, term);
}

fn appendTensorOnlyProgramTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), program: *const TensorOnlyProgram, term_index: u16) !rendering.RationalId {
    if (term_index >= program.term_count) return error.ProjectorConstructorTermOutOfBounds;
    if (term_index >= program.merged_terms.len) return error.ProjectorConstructorTermOutOfBounds;
    return appendVectorBrauerTermAtoms(allocator, atoms, program.merged_terms[term_index]);
}

fn tensorOnlyActivePairSlotForTerm(program: *const TensorOnlyProgram, term_index: u16) !usize {
    var low: u16 = 0;
    var high = program.active_pair_term_count;
    while (low < high) {
        const middle = low + (high - low) / 2;
        const pair_slot = program.active_pair_term_indices[middle];
        const pair_index = program.pair_term_indices[pair_slot];
        if (term_index < pair_index.first_term) {
            high = middle;
            continue;
        }
        const pair_end = @as(u32, pair_index.first_term) + pair_index.term_count;
        if (@as(u32, term_index) >= pair_end) {
            low = middle + 1;
            continue;
        }
        return pair_slot;
    }
    return error.ProjectorConstructorTermOutOfBounds;
}

fn tensorOnlyActionWordPairTerm(channel: TensorOnlyChannel, left_word: TensorEndpointActionWord, right_word: TensorEndpointActionWord, coefficient: Rational) !VectorBrauerTerm {
    var term = try vectorBrauerTerm(coefficient);
    const right_adjoint = channel.input_slot_count == channel.output_slot_count;
    try appendTensorOnlyBrauerWordTermAtoms(&term, channel, left_word.word, false);
    try appendTensorEndpointActionWordHodgeAtoms(&term, left_word);
    try appendTensorOnlyBrauerWordTermAtoms(&term, channel, right_word.word, right_adjoint);
    try appendTensorEndpointActionWordHodgeAtoms(&term, right_word);
    canonicalizeVectorBrauerTerm(&term);
    return term;
}

fn appendTensorOnlyBrauerWordTermAtoms(term: *VectorBrauerTerm, channel: TensorOnlyChannel, word: BrauerWord, adjoint: bool) !void {
    var edge_index: u8 = 0;
    while (edge_index < word.edge_count) : (edge_index += 1) {
        const edge = word.edges[edge_index];
        switch (edge.kind) {
            .delta => try tensorOnlyTermDelta(term, channel, edge.input_a, edge.output_a),
            .input_trace => if (adjoint)
                try tensorOnlyTermOutputMetric(term, channel, edge.input_a, edge.input_b)
            else
                try tensorOnlyTermInputMetric(term, channel, edge.input_a, edge.input_b),
            .output_metric => if (adjoint)
                try tensorOnlyTermInputMetric(term, channel, edge.output_a, edge.output_b)
            else
                try tensorOnlyTermOutputMetric(term, channel, edge.output_a, edge.output_b),
        }
    }
}

fn appendTensorEndpointActionWordHodgeAtoms(term: *VectorBrauerTerm, action: TensorEndpointActionWord) !void {
    var hodge_index: u8 = 0;
    while (hodge_index < action.hodge_count) : (hodge_index += 1) {
        const hodge = action.hodge_actions[hodge_index];
        try vectorBrauerTermHodgeStar(term, hodge.block, hodge.block);
    }
}

fn tensorOnlyTermDelta(term: *VectorBrauerTerm, channel: TensorOnlyChannel, input: u8, output: u8) !void {
    const source = try tensorOnlyInputSlotSource(channel, input);
    const target = try tensorOnlyOutputSlotSource(channel, output);
    try vectorBrauerTermDelta(term, source.block, source.slot, target.block, target.slot);
}

fn tensorOnlyTermInputMetric(term: *VectorBrauerTerm, channel: TensorOnlyChannel, left: u8, right: u8) !void {
    const left_source = try tensorOnlyInputSlotSource(channel, left);
    const right_source = try tensorOnlyInputSlotSource(channel, right);
    try vectorBrauerTermMetric(term, left_source.block, left_source.slot, right_source.block, right_source.slot);
}

fn tensorOnlyTermOutputMetric(term: *VectorBrauerTerm, channel: TensorOnlyChannel, left: u8, right: u8) !void {
    const left_source = try tensorOnlyOutputSlotSource(channel, left);
    const right_source = try tensorOnlyOutputSlotSource(channel, right);
    try vectorBrauerTermMetric(term, left_source.block, left_source.slot, right_source.block, right_source.slot);
}

fn tensorOnlyInputSlotSource(channel: TensorOnlyChannel, input: u8) !VectorSlotSource {
    if (input < channel.left.slot_count) return tensorOnlyEndpointSlotSource(channel.left, input);
    const right_slot = input - channel.left.slot_count;
    if (right_slot < channel.right.slot_count) return tensorOnlyEndpointSlotSource(channel.right, right_slot);
    return error.ProjectorWordTooLarge;
}

fn tensorOnlyOutputSlotSource(channel: TensorOnlyChannel, output: u8) !VectorSlotSource {
    if (output >= channel.output.slot_count) return error.ProjectorWordTooLarge;
    return tensorOnlyEndpointSlotSource(channel.output, output);
}

fn tensorOnlyEndpointSlotSource(endpoint: TensorOnlyEndpoint, slot: u8) !VectorSlotSource {
    if (slot >= endpoint.layout.slot_count) return error.ProjectorWordTooLarge;
    const mapped = endpoint.layout.slots[slot];
    return .{ .block = mapped.block, .slot = mapped.slot };
}

fn explicitEndpoint(side: TensorEndpointSide, block: rendering.IndexRef, descriptor: OrthogonalTensorDescriptor) !ExplicitEndpoint {
    const vector_slot_count = descriptorExplicitVectorSlotCount(descriptor) orelse 0;
    if (vector_slot_count > max_vector_young_boxes) return error.UnsupportedTensorShapeOverCap;
    return .{
        .side = side,
        .block = block,
        .descriptor = descriptor,
        .vector_slot_count = vector_slot_count,
        .has_spinor = descriptor.has_spinor,
    };
}

fn vectorSlotProjectorSpecFromStructural(spec: StructuralProjectorSpec) ?VectorSlotProjectorSpec {
    const channel = tensorCompilerChannelFromStructural(spec) catch return null;
    return vectorSlotProjectorSpecFromChannel(channel);
}

fn vectorSlotProjectorSpecFromChannel(channel: TensorCompilerChannel) ?VectorSlotProjectorSpec {
    const left_slot_count = descriptorExplicitVectorSlotCount(channel.left.descriptor) orelse return null;
    const right_slot_count = descriptorExplicitVectorSlotCount(channel.right.descriptor) orelse return null;
    const output_shape = descriptorExplicitVectorShape(channel.output.descriptor) orelse return null;
    if (left_slot_count + right_slot_count != output_shape.box_count) return null;
    return .{
        .operator_id = channel.operator_id,
        .dimension = channel.dimension,
        .left = channel.left.block,
        .left_slot_count = left_slot_count,
        .left_form_profile = descriptorSourceFormProfile(channel.left.descriptor),
        .right = channel.right.block,
        .right_slot_count = right_slot_count,
        .right_form_profile = descriptorSourceFormProfile(channel.right.descriptor),
        .output = channel.output.block,
        .output_form_profile = descriptorTargetFormProfile(channel.output.descriptor),
        .shape = output_shape,
    };
}

fn tensorPairingSpecFromStructural(spec: StructuralProjectorSpec) ?TensorPairingSpec {
    const channel = tensorCompilerChannelFromStructural(spec) catch return null;
    return tensorPairingSpecFromChannel(channel);
}

fn tensorPairingSpecFromChannel(channel: TensorCompilerChannel) ?TensorPairingSpec {
    if (channel.output.descriptor.kind != .scalar) return null;
    const left_shape = descriptorExplicitVectorShape(channel.left.descriptor) orelse return null;
    const right_shape = descriptorExplicitVectorShape(channel.right.descriptor) orelse return null;
    if (!youngShapeEql(left_shape, right_shape)) return null;
    return .{
        .operator_id = channel.operator_id,
        .dimension = channel.dimension,
        .left = channel.left.block,
        .left_form_profile = descriptorSourceFormProfile(channel.left.descriptor),
        .right = channel.right.block,
        .right_form_profile = descriptorSourceFormProfile(channel.right.descriptor),
        .shape = left_shape,
    };
}

fn tensorContractionSpecFromChannel(channel: TensorCompilerChannel) ?TensorContractionSpec {
    const left_slot_count = descriptorExplicitVectorSlotCount(channel.left.descriptor) orelse return null;
    const right_slot_count = descriptorExplicitVectorSlotCount(channel.right.descriptor) orelse return null;
    const output_shape = descriptorExplicitVectorShape(channel.output.descriptor) orelse return null;
    const input_count = left_slot_count + right_slot_count;
    const contraction_count = tensorContractionCountForSlots(input_count, output_shape.box_count) orelse return null;
    if (contraction_count > left_slot_count or contraction_count > right_slot_count) return null;
    return .{
        .operator_id = channel.operator_id,
        .dimension = channel.dimension,
        .left = channel.left.block,
        .left_slot_count = left_slot_count,
        .left_form_profile = descriptorSourceFormProfile(channel.left.descriptor),
        .right = channel.right.block,
        .right_slot_count = right_slot_count,
        .right_form_profile = descriptorSourceFormProfile(channel.right.descriptor),
        .output = channel.output.block,
        .output_form_profile = descriptorTargetFormProfile(channel.output.descriptor),
        .shape = output_shape,
        .contraction_count = contraction_count,
    };
}

fn tensorContractionCountForSlots(input_count: u8, output_count: u8) ?u8 {
    if (input_count <= output_count) return null;
    const contracted_slots = input_count - output_count;
    if (@mod(contracted_slots, 2) != 0) return null;
    const contraction_count = contracted_slots / 2;
    return if (contraction_count == 0) null else contraction_count;
}

fn vectorProjectorSpecForContraction(spec: TensorContractionSpec) VectorSlotProjectorSpec {
    return .{
        .operator_id = spec.operator_id,
        .dimension = spec.dimension,
        .left = spec.left,
        .left_slot_count = spec.left_slot_count,
        .left_form_profile = spec.left_form_profile,
        .right = spec.right,
        .right_slot_count = spec.right_slot_count,
        .right_form_profile = spec.right_form_profile,
        .output = spec.output,
        .output_form_profile = spec.output_form_profile,
        .shape = spec.shape,
    };
}

fn tensorContractionSpecFromVectorSpec(spec: VectorSlotProjectorSpec) TensorContractionSpec {
    const input_count = spec.left_slot_count + spec.right_slot_count;
    return .{
        .operator_id = spec.operator_id,
        .dimension = spec.dimension,
        .left = spec.left,
        .left_slot_count = spec.left_slot_count,
        .left_form_profile = spec.left_form_profile,
        .right = spec.right,
        .right_slot_count = spec.right_slot_count,
        .right_form_profile = spec.right_form_profile,
        .output = spec.output,
        .output_form_profile = spec.output_form_profile,
        .shape = spec.shape,
        .contraction_count = tensorContractionCountForSlots(input_count, spec.shape.box_count) orelse 0,
    };
}

fn youngShapeEql(left: YoungShape, right: YoungShape) bool {
    if (left.row_count != right.row_count or left.box_count != right.box_count) return false;
    var row: u8 = 0;
    while (row < left.row_count) : (row += 1) {
        if (left.rows[row] != right.rows[row]) return false;
    }
    return true;
}

fn tensorDescriptorFromStructuralEndpoint(endpoint: StructuralEndpoint, dimension: u16) anyerror!OrthogonalTensorDescriptor {
    var descriptor: OrthogonalTensorDescriptor = .{
        .kind = .scalar,
        .dimension = dimension,
        .form_profile = endpoint.form_profile,
        .form_mask = endpoint.form_mask,
        .form_rank = endpoint.form_rank,
        .form_duality = endpoint.form_duality,
        .has_spinor = endpoint.has_spinor,
        .chirality = endpoint.chirality,
        .tower_power = endpoint.tower_power,
    };
    if (endpoint.has_spinor) {
        descriptor.kind = if (endpoint.form_count != 0 or endpoint.young_row_count != 0) .tensor_spinor else .spinor;
        return descriptor;
    }
    if (endpoint.young_row_count != 0) {
        try validateYoungRows(endpoint.young_row_count, endpoint.young_rows);
        const box_count = try youngBoxCount(endpoint.young_row_count, endpoint.young_rows);
        if (box_count != endpoint.young_box_count) return error.InvalidYoungShape;
        if (box_count > max_tensor_young_boxes) return error.UnsupportedTensorShapeOverCap;
        const is_exterior = youngRowsAreSingleColumn(endpoint.young_row_count, endpoint.young_rows);
        try validateExplicitYoungFormMetadata(endpoint, box_count, is_exterior);
        descriptor.kind = if (is_exterior) .exterior_form else .vector_young;
        descriptor.young_row_count = endpoint.young_row_count;
        descriptor.young_rows = endpoint.young_rows;
        descriptor.young_box_count = box_count;
        descriptor.column_count = try transposeYoungRows(endpoint.young_row_count, endpoint.young_rows, &descriptor.column_heights);
        if (descriptor.kind == .exterior_form) {
            descriptor.form_rank = box_count;
            descriptor.form_profile = if (box_count == 0) 0 else profileIncrementedRank(0, box_count);
            descriptor.form_mask = if (box_count == 0 or box_count > 64) 0 else @as(u64, 1) << @intCast(box_count - 1);
        }
        return descriptor;
    }
    if (try structuralEndpointSingleFormRank(endpoint)) |form_rank| {
        var rows = [_]u8{0} ** max_young_rows;
        var row: u8 = 0;
        while (row < form_rank) : (row += 1) {
            rows[row] = 1;
        }
        descriptor.kind = .exterior_form;
        descriptor.young_row_count = form_rank;
        descriptor.young_rows = rows;
        descriptor.young_box_count = form_rank;
        descriptor.column_count = 1;
        descriptor.column_heights[0] = form_rank;
        descriptor.form_rank = form_rank;
        descriptor.form_profile = profileIncrementedRank(0, form_rank);
        descriptor.form_mask = @as(u64, 1) << @intCast(form_rank - 1);
        return descriptor;
    }
    if (endpoint.form_count != 0) {
        descriptor.kind = .mixed_tensor_form;
        const shape = try profileYoungShape(endpoint.form_profile);
        descriptor.young_row_count = shape.row_count;
        descriptor.young_rows = shape.rows;
        descriptor.young_box_count = shape.box_count;
        descriptor.column_count = try transposeYoungRows(shape.row_count, shape.rows, &descriptor.column_heights);
    }
    return descriptor;
}

fn validateExplicitYoungFormMetadata(endpoint: StructuralEndpoint, box_count: u8, is_exterior: bool) !void {
    const has_form_metadata = endpoint.form_count != 0 or
        endpoint.form_rank != 0 or
        endpoint.form_profile != 0 or
        endpoint.form_mask != 0 or
        endpoint.form_duality != .none;
    if (!has_form_metadata) return;
    if (!is_exterior) {
        if (endpoint.form_duality != .none or endpoint.form_profile == 0) return error.InvalidFormProfile;
        if ((try profileVectorSlotCount(endpoint.form_profile)) != box_count) return error.InvalidFormProfile;
        const profile_count = profileTotalPower(endpoint.form_profile);
        const profile_rank_count: u16 = @popCount(profileMask(endpoint.form_profile));
        if (endpoint.form_count != 0 and endpoint.form_count != profile_count and endpoint.form_count != profile_rank_count) return error.InvalidFormProfile;
        if (endpoint.form_mask != 0 and endpoint.form_mask != profileMask(endpoint.form_profile)) return error.InvalidFormProfile;
        if (endpoint.form_rank != 0 and profileSlot(endpoint.form_profile, endpoint.form_rank - 1) == 0) return error.InvalidFormProfile;
        return;
    }
    if (endpoint.form_count != 0 and endpoint.form_count != 1) return error.InvalidFormProfile;
    if (endpoint.form_rank != 0 and endpoint.form_rank != box_count) return error.InvalidFormProfile;
    const expected_profile = profileIncrementedRank(0, box_count);
    const expected_mask = @as(u64, 1) << @intCast(box_count - 1);
    if (endpoint.form_profile != 0 and endpoint.form_profile != expected_profile) return error.InvalidFormProfile;
    if (endpoint.form_mask != 0 and endpoint.form_mask != expected_mask) return error.InvalidFormProfile;
}

fn descriptorExplicitVectorSlotCount(descriptor: OrthogonalTensorDescriptor) ?u8 {
    if (descriptor.has_spinor or descriptor.form_duality != .none) return null;
    return switch (descriptor.kind) {
        .scalar => 0,
        .vector_young, .exterior_form => descriptor.young_box_count,
        .mixed_tensor_form => descriptor.young_box_count,
        else => null,
    };
}

fn descriptorSourceFormProfile(descriptor: OrthogonalTensorDescriptor) u128 {
    return switch (descriptor.kind) {
        .exterior_form, .mixed_tensor_form => descriptor.form_profile,
        else => 0,
    };
}

fn descriptorTargetFormProfile(descriptor: OrthogonalTensorDescriptor) u128 {
    return switch (descriptor.kind) {
        .exterior_form, .mixed_tensor_form => descriptor.form_profile,
        else => 0,
    };
}

fn descriptorExplicitVectorShape(descriptor: OrthogonalTensorDescriptor) ?YoungShape {
    if (descriptor.has_spinor or descriptor.form_duality != .none) return null;
    switch (descriptor.kind) {
        .vector_young, .exterior_form, .mixed_tensor_form => {
            if (descriptor.young_box_count == 0) return null;
            return .{
                .row_count = descriptor.young_row_count,
                .rows = descriptor.young_rows,
                .box_count = descriptor.young_box_count,
            };
        },
        else => return null,
    }
}

fn structuralEndpointSingleFormRank(endpoint: StructuralEndpoint) !?u8 {
    if (endpoint.form_count != 1) return null;
    var form_rank = endpoint.form_rank;
    if (form_rank == 0) {
        form_rank = profileOnlyRank(endpoint.form_profile) orelse return null;
    }
    if (form_rank == 0) return null;
    if (form_rank > max_vector_young_boxes) return error.UnsupportedTensorShapeOverCap;
    const expected_profile = profileIncrementedRank(0, form_rank);
    const expected_mask = @as(u64, 1) << @intCast(form_rank - 1);
    if (endpoint.form_profile != 0 and endpoint.form_profile != expected_profile) return error.InvalidFormProfile;
    if (endpoint.form_mask != 0 and endpoint.form_mask != expected_mask) return error.InvalidFormProfile;
    return form_rank;
}

fn profileVectorSlotCount(profile: u128) !u8 {
    var total: u16 = 0;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const count = profileSlot(profile, rank_index);
        if (count == 0) continue;
        total += @as(u16, count) * (@as(u16, rank_index) + 1);
        if (total > max_vector_young_boxes) return error.UnsupportedTensorShapeOverCap;
    }
    return @intCast(total);
}

fn profileYoungShape(profile: u128) !YoungShape {
    var shape: YoungShape = .{};
    var row_index: u8 = 0;
    while (row_index < max_young_rows) : (row_index += 1) {
        var row_len: u8 = 0;
        var rank_index: u8 = 0;
        while (rank_index < 32) : (rank_index += 1) {
            const count = profileSlot(profile, rank_index);
            if (count == 0) continue;
            if (rank_index >= row_index) row_len += count;
        }
        if (row_len == 0) break;
        shape.rows[row_index] = row_len;
        shape.row_count = row_index + 1;
        shape.box_count += row_len;
        if (shape.box_count > max_vector_young_boxes) return error.UnsupportedTensorShapeOverCap;
    }
    const total = try profileVectorSlotCount(profile);
    if (shape.box_count != total) return error.UnsupportedTensorShapeOverCap;
    return shape;
}

fn orthogonalTensorDescriptorFromDynkin(simple: symmetry.SimpleLieAlgebra, labels: []const i16) !OrthogonalTensorDescriptor {
    if (labels.len != simple.rank or labels.len > max_tensor_label_rank) return error.InvalidDynkinRank;
    return switch (simple.family) {
        .b => bTensorDescriptorFromDynkin(simple, labels),
        .d => dTensorDescriptorFromDynkin(simple, labels),
        else => error.UnsupportedTensorFamily,
    };
}

fn bTensorDescriptorFromDynkin(simple: symmetry.SimpleLieAlgebra, labels: []const i16) !OrthogonalTensorDescriptor {
    if (simple.rank == 0 or labels.len != simple.rank) return error.InvalidDynkinRank;
    const spin_label = labels[labels.len - 1];
    if (spin_label < 0) return error.InvalidDynkinLabel;
    if (@mod(spin_label, 2) != 0) return error.UnsupportedTensorSpinorLabel;

    var rows = [_]u8{0} ** max_young_rows;
    var row_count: u8 = 0;
    var row_index: usize = 0;
    while (row_index < labels.len) : (row_index += 1) {
        var value: i32 = @divExact(@as(i32, spin_label), 2);
        var label_index = row_index;
        while (label_index + 1 < labels.len) : (label_index += 1) {
            if (labels[label_index] < 0) return error.InvalidDynkinLabel;
            value += labels[label_index];
        }
        if (value < 0 or value > std.math.maxInt(u8)) return error.UnsupportedTensorShapeOverCap;
        rows[row_index] = @intCast(value);
        if (value != 0) row_count = @intCast(row_index + 1);
    }
    return descriptorFromTensorRows(simple, labels, row_count, rows, .none);
}

fn dTensorDescriptorFromDynkin(simple: symmetry.SimpleLieAlgebra, labels: []const i16) !OrthogonalTensorDescriptor {
    if (simple.rank < 2 or labels.len != simple.rank) return error.InvalidDynkinRank;
    const left_spin = labels[labels.len - 2];
    const right_spin = labels[labels.len - 1];
    if (left_spin < 0 or right_spin < 0) return error.InvalidDynkinLabel;
    if (@mod(left_spin + right_spin, 2) != 0) return error.UnsupportedTensorSpinorLabel;

    const spin_half_sum: i32 = @divExact(@as(i32, left_spin) + @as(i32, right_spin), 2);
    var rows = [_]u8{0} ** max_young_rows;
    var row_count: u8 = 0;
    var row_index: usize = 0;
    while (row_index + 2 < labels.len) : (row_index += 1) {
        var value = spin_half_sum;
        var label_index = row_index;
        while (label_index + 2 < labels.len) : (label_index += 1) {
            if (labels[label_index] < 0) return error.InvalidDynkinLabel;
            value += labels[label_index];
        }
        if (value < 0 or value > std.math.maxInt(u8)) return error.UnsupportedTensorShapeOverCap;
        rows[row_index] = @intCast(value);
        if (value != 0) row_count = @intCast(row_index + 1);
    }
    if (spin_half_sum != 0) {
        if (labels.len - 1 >= max_young_rows) return error.UnsupportedTensorShapeOverCap;
        rows[labels.len - 2] = @intCast(spin_half_sum);
        row_count = @max(row_count, @as(u8, @intCast(labels.len - 1)));
    }

    const duality: rendering.DualityTag = if (left_spin == right_spin) .none else if (left_spin > right_spin) .self_dual else .anti_self_dual;
    return descriptorFromTensorRows(simple, labels, row_count, rows, duality);
}

fn descriptorFromTensorRows(simple: symmetry.SimpleLieAlgebra, labels: []const i16, row_count: u8, rows: [max_young_rows]u8, duality: rendering.DualityTag) !OrthogonalTensorDescriptor {
    try validateYoungRows(row_count, rows);
    const box_count = try youngBoxCount(row_count, rows);
    if (box_count > max_tensor_young_boxes) return error.UnsupportedTensorShapeOverCap;

    var descriptor: OrthogonalTensorDescriptor = .{
        .kind = if (box_count == 0) .scalar else if (youngRowsAreSingleColumn(row_count, rows)) .exterior_form else .vector_young,
        .family = simple.family,
        .rank = simple.rank,
        .dimension = rendering.orthogonalDimension(simple),
        .label_count = @intCast(labels.len),
        .young_row_count = row_count,
        .young_rows = rows,
        .young_box_count = box_count,
        .form_duality = duality,
    };
    var index: usize = 0;
    while (index < labels.len) : (index += 1) {
        descriptor.labels[index] = labels[index];
    }
    descriptor.column_count = try transposeYoungRows(row_count, rows, &descriptor.column_heights);
    if (descriptor.kind == .exterior_form) {
        descriptor.form_rank = box_count;
        descriptor.form_profile = if (box_count == 0) 0 else profileIncrementedRank(0, box_count);
        descriptor.form_mask = if (box_count == 0 or box_count > 64) 0 else @as(u64, 1) << @intCast(box_count - 1);
    }
    return descriptor;
}

fn validateYoungRows(row_count: u8, rows: [max_young_rows]u8) !void {
    if (row_count > max_young_rows) return error.UnsupportedTensorShapeOverCap;
    var previous: u8 = std.math.maxInt(u8);
    var index: u8 = 0;
    while (index < row_count) : (index += 1) {
        const row = rows[index];
        if (row == 0 or row > previous) return error.InvalidYoungShape;
        previous = row;
    }
    while (index < max_young_rows) : (index += 1) {
        if (rows[index] != 0) return error.InvalidYoungShape;
    }
}

fn youngBoxCount(row_count: u8, rows: [max_young_rows]u8) !u8 {
    var count: u16 = 0;
    var index: u8 = 0;
    while (index < row_count) : (index += 1) {
        count += rows[index];
    }
    if (count > std.math.maxInt(u8)) return error.UnsupportedTensorShapeOverCap;
    return @intCast(count);
}

fn youngRowsAreSingleColumn(row_count: u8, rows: [max_young_rows]u8) bool {
    if (row_count == 0) return false;
    var index: u8 = 0;
    while (index < row_count) : (index += 1) {
        if (rows[index] != 1) return false;
    }
    return true;
}

fn transposeYoungRows(row_count: u8, rows: [max_young_rows]u8, out: *[max_young_rows]u8) !u8 {
    out.* = [_]u8{0} ** max_young_rows;
    if (row_count == 0) return 0;
    const column_count = rows[0];
    if (column_count > max_young_rows) return error.UnsupportedTensorShapeOverCap;
    var column: u8 = 0;
    while (column < column_count) : (column += 1) {
        var height: u8 = 0;
        var row: u8 = 0;
        while (row < row_count) : (row += 1) {
            if (rows[row] > column) height += 1;
        }
        out[column] = height;
    }
    return column_count;
}

fn vectorSlotProjectorTermCount(spec: VectorSlotProjectorSpec) u16 {
    return countVectorYoungProjectionTerms(spec) catch 0;
}

fn tensorPairingTermCount(spec: TensorPairingSpec) u16 {
    return countVectorYoungProjectionTerms(vectorProjectorSpecForPairing(spec)) catch 0;
}

fn appendVectorSlotProjectorTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: VectorSlotProjectorSpec, term_index: u16) !rendering.RationalId {
    const term = try vectorYoungProjectionTermAt(spec, term_index);
    return appendVectorBrauerTermAtoms(allocator, atoms, term);
}

fn appendVectorBrauerProgramTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), program: VectorBrauerProgram, term_index: u16) !rendering.RationalId {
    if (term_index >= program.term_count) return error.ProjectorConstructorTermOutOfBounds;
    return appendVectorBrauerTermAtoms(allocator, atoms, program.terms[term_index]);
}

fn appendVectorBrauerTermAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), term: VectorBrauerTerm) !rendering.RationalId {
    var atom_index: u8 = 0;
    while (atom_index < term.atom_count) : (atom_index += 1) {
        const atom = term.atoms[atom_index];
        switch (atom.kind) {
            .delta => try atoms.append(allocator, .{ .vector_slot_delta = .{
                .upper = atom.upper,
                .upper_slot = atom.upper_slot,
                .lower = atom.lower,
                .lower_slot = atom.lower_slot,
            } }),
            .metric => try atoms.append(allocator, .{ .vector_slot_metric = .{
                .left = atom.left,
                .left_slot = atom.left_slot,
                .right = atom.right,
                .right_slot = atom.right_slot,
            } }),
            .hodge_star => try atoms.append(allocator, .{ .hodge_star = .{
                .input = atom.hodge_input,
                .output = atom.hodge_output,
            } }),
        }
    }
    return rationalToRenderingId(term.coefficient);
}

fn appendTensorPairingTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorPairingSpec, term_index: u16) !rendering.RationalId {
    const term = try vectorYoungProjectionTermAt(vectorProjectorSpecForPairing(spec), term_index);
    return appendTensorPairingBrauerTermAtoms(allocator, atoms, term);
}

fn appendTensorPairingProgramTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), program: VectorBrauerProgram, term_index: u16) !rendering.RationalId {
    if (term_index >= program.term_count) return error.ProjectorConstructorTermOutOfBounds;
    return appendTensorPairingBrauerTermAtoms(allocator, atoms, program.terms[term_index]);
}

fn appendTensorPairingBrauerTermAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), term: VectorBrauerTerm) !rendering.RationalId {
    var atom_index: u8 = 0;
    while (atom_index < term.atom_count) : (atom_index += 1) {
        const atom = term.atoms[atom_index];
        switch (atom.kind) {
            .delta => try atoms.append(allocator, .{ .vector_slot_metric = .{
                .left = atom.upper,
                .left_slot = atom.upper_slot,
                .right = atom.lower,
                .right_slot = atom.lower_slot,
            } }),
            .metric => try atoms.append(allocator, .{ .vector_slot_metric = .{
                .left = atom.left,
                .left_slot = atom.left_slot,
                .right = atom.right,
                .right_slot = atom.right_slot,
            } }),
            .hodge_star => return error.UnsupportedTensorBridge,
        }
    }
    return rationalToRenderingId(term.coefficient);
}

fn vectorProjectorSpecForPairing(spec: TensorPairingSpec) VectorSlotProjectorSpec {
    return .{
        .operator_id = spec.operator_id,
        .dimension = spec.dimension,
        .left = spec.left,
        .left_slot_count = spec.shape.box_count,
        .left_form_profile = spec.left_form_profile,
        .right = 0,
        .right_slot_count = 0,
        .output = spec.right,
        .output_form_profile = spec.right_form_profile,
        .shape = spec.shape,
    };
}

fn compileTensorContractionBrauerCore(spec: TensorContractionSpec) !VectorBrauerProgram {
    const input_count = spec.left_slot_count + spec.right_slot_count;
    if (spec.contraction_count == 0) return error.UnsupportedTensorBridge;
    if (@as(u16, input_count) != @as(u16, spec.shape.box_count) + 2 * @as(u16, spec.contraction_count)) return error.UnsupportedTensorBridge;
    if (spec.contraction_count > spec.left_slot_count or spec.contraction_count > spec.right_slot_count) return error.UnsupportedTensorBridge;
    if (input_count > max_vector_young_boxes or spec.shape.box_count > max_vector_young_boxes) return error.UnsupportedTensorShapeOverCap;

    var candidates: BrauerCandidateBuffer = .{};
    try enumerateTensorContractionCandidates(spec, &candidates);
    if (candidates.count == 0) return error.UnsupportedStructuralProjectorTerm;

    var program: VectorBrauerProgram = .{};
    try compileTensorContractionGram(&program, spec, candidates);
    return program;
}

fn enumerateTensorContractionCandidates(spec: TensorContractionSpec, out: *BrauerCandidateBuffer) !void {
    var projector = try outputTraceFreeBrauerProjector(spec.shape, spec.dimension);
    defer projector.deinit();
    var pairing: TensorContractionPairing = .{};
    try enumerateTensorContractionPairings(spec, projector, 0, &pairing, out);
    try uniqueBrauerWords(out);
}

fn enumerateTensorContractionPairings(spec: TensorContractionSpec, projector: TraceFreeBrauerProjector, start_left_slot: u8, pairing: *TensorContractionPairing, out: *BrauerCandidateBuffer) !void {
    if (pairing.count == spec.contraction_count) {
        var candidate: BrauerCandidate = .{};
        try appendTensorContractionProjectorCandidate(&candidate, spec, projector, pairing.*);
        try uniqueBrauerCandidateWords(&candidate);
        if (candidate.word_count != 0) try out.append(candidate);
        return;
    }

    var left_slot = start_left_slot;
    while (left_slot < spec.left_slot_count) : (left_slot += 1) {
        if (pairing.containsLeft(left_slot)) continue;
        var right_slot: u8 = 0;
        while (right_slot < spec.right_slot_count) : (right_slot += 1) {
            if (pairing.containsRight(right_slot)) continue;
            try pairing.append(left_slot, right_slot);
            try enumerateTensorContractionPairings(spec, projector, left_slot + 1, pairing, out);
            pairing.pop();
        }
    }
}

fn outputTraceFreeBrauerProjector(shape: YoungShape, dimension: u16) !TraceFreeBrauerProjector {
    if (shape.box_count > max_vector_young_boxes) return error.UnsupportedTensorShapeOverCap;
    var young_candidates: BrauerCandidateBuffer = .{};
    try appendVectorYoungPermutationCandidates(shape, shape.box_count, &young_candidates);
    try uniqueBrauerWords(&young_candidates);
    if (young_candidates.count == 0) return error.UnsupportedTensorBridge;
    return traceFreeBrauerProjectorBasisForShape(shape, dimension, young_candidates.candidates[0]);
}

fn appendTensorContractionProjectorCandidate(candidate: *BrauerCandidate, spec: TensorContractionSpec, projector: TraceFreeBrauerProjector, pairing: TensorContractionPairing) !void {
    var remaining = [_]u8{0} ** max_vector_young_boxes;
    const input_count = spec.left_slot_count + spec.right_slot_count;
    var remaining_count: u8 = 0;
    var input_slot: u8 = 0;
    while (input_slot < input_count) : (input_slot += 1) {
        if (pairing.containsInput(spec.left_slot_count, input_slot)) continue;
        remaining[remaining_count] = input_slot;
        remaining_count += 1;
    }
    if (remaining_count != spec.shape.box_count) return error.UnsupportedTensorBridge;

    var basis_index: u8 = 0;
    while (basis_index < projector.basis_count) : (basis_index += 1) {
        const scale = projector.coefficients[basis_index];
        if (scale.numerator == 0) continue;
        const basis = projector.basis[basis_index];
        var word_index: u8 = 0;
        while (word_index < basis.word_count) : (word_index += 1) {
            var word = try remapTensorContractionProjectorWord(basis.words[word_index], remaining, remaining_count, spec.left_slot_count, pairing);
            word.coefficient = try word.coefficient.mul(scale);
            try appendMergedBrauerWord(candidate, word);
        }
    }
}

fn remapTensorContractionProjectorWord(projector_word: BrauerWord, remaining: [max_vector_young_boxes]u8, remaining_count: u8, left_slot_count: u8, pairing: TensorContractionPairing) !BrauerWord {
    var word: BrauerWord = .{ .coefficient = projector_word.coefficient };
    var pairing_index: u8 = 0;
    while (pairing_index < pairing.count) : (pairing_index += 1) {
        try appendBrauerInputTraceEdge(&word, pairing.left_slots[pairing_index], left_slot_count + pairing.right_slots[pairing_index]);
    }
    var edge_index: u8 = 0;
    while (edge_index < projector_word.edge_count) : (edge_index += 1) {
        const edge = projector_word.edges[edge_index];
        switch (edge.kind) {
            .delta => {
                if (edge.input_a >= remaining_count) return error.UnsupportedTensorBridge;
                try appendBrauerDeltaEdge(&word, remaining[edge.input_a], edge.output_a);
            },
            .input_trace => {
                if (edge.input_a >= remaining_count or edge.input_b >= remaining_count) return error.UnsupportedTensorBridge;
                try appendBrauerInputTraceEdge(&word, remaining[edge.input_a], remaining[edge.input_b]);
            },
            .output_metric => try appendBrauerOutputMetricEdge(&word, edge.output_a, edge.output_b),
        }
    }
    return word;
}

fn compileTensorContractionGram(program: *VectorBrauerProgram, spec: TensorContractionSpec, candidates: BrauerCandidateBuffer) !void {
    var gram: [max_vector_brauer_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_vector_brauer_gram_entries;
    var row: usize = 0;
    while (row < candidates.count) : (row += 1) {
        var column: usize = 0;
        while (column <= row) : (column += 1) {
            const value = try tensorContractionCandidateInnerProduct(spec, candidates.candidates[row], candidates.candidates[column]);
            gram[row * candidates.count + column] = value;
            gram[column * candidates.count + row] = value;
        }
    }

    const pivots = try selectVectorBrauerGramPivots(candidates.count, gram[0..]);
    if (pivots.count == 0) return error.SingularGramMatrix;
    var pivot_gram: [max_vector_brauer_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_vector_brauer_gram_entries;
    row = 0;
    while (row < pivots.count) : (row += 1) {
        var column: usize = 0;
        while (column < pivots.count) : (column += 1) {
            pivot_gram[row * pivots.count + column] = gram[@as(usize, pivots.pivots[row]) * candidates.count + pivots.pivots[column]];
        }
    }

    program.candidate_count = candidates.count;
    program.pivot_count = pivots.count;
    program.candidates = candidates.candidates;
    var pivot_index: u8 = 0;
    while (pivot_index < pivots.count) : (pivot_index += 1) {
        program.pivots[pivot_index] = pivots.pivots[pivot_index];
    }
    program.inverse_gram = try invertVectorBrauerGram(pivots.count, pivot_gram[0..]);
}

fn compileVectorYoungBrauerCore(spec: VectorSlotProjectorSpec) !VectorBrauerProgram {
    if (spec.shape.box_count > max_vector_young_boxes) return error.UnsupportedTensorShapeOverCap;
    const rank = vectorYoungRank(spec) orelse return error.UnsupportedStructuralProjectorTerm;
    if (rank > max_vector_young_boxes) return error.UnsupportedTensorShapeOverCap;

    var candidates: BrauerCandidateBuffer = .{};
    try enumerateVectorYoungCandidates(spec, rank, &candidates);
    if (candidates.count == 0) return error.UnsupportedStructuralProjectorTerm;

    var program: VectorBrauerProgram = .{};
    try compileVectorBrauerGram(&program, candidates, rank, spec.dimension);
    return program;
}

fn compileVectorYoungBrauerProgram(spec: VectorSlotProjectorSpec) !VectorBrauerProgram {
    var program = try compileVectorYoungBrauerCore(spec);
    try appendVectorYoungProjectionTerms(&program, spec);
    if (program.term_count == 0) return error.UnsupportedStructuralProjectorTerm;
    return program;
}

fn vectorYoungRank(spec: VectorSlotProjectorSpec) ?u8 {
    const input_count = spec.left_slot_count + spec.right_slot_count;
    if (spec.shape.row_count == 0) return if (input_count == 2) input_count else null;
    if (spec.shape.box_count != input_count) return null;
    return spec.shape.box_count;
}

fn enumerateVectorYoungCandidates(spec: VectorSlotProjectorSpec, rank: u8, out: *BrauerCandidateBuffer) !void {
    const shape = try normalizedVectorYoungShape(spec, rank);
    try appendVectorYoungPermutationCandidates(shape, rank, out);
    try appendVectorYoungTraceCandidates(rank, out);
    try uniqueBrauerWords(out);
}

fn normalizedVectorYoungShape(spec: VectorSlotProjectorSpec, rank: u8) !YoungShape {
    if (spec.shape.row_count != 0) return spec.shape;
    if (rank != 2) return error.UnsupportedStructuralProjectorTerm;
    return .{
        .row_count = 2,
        .rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 },
        .box_count = 2,
    };
}

fn appendVectorYoungPermutationCandidates(shape: YoungShape, rank: u8, out: *BrauerCandidateBuffer) !void {
    if (shape.box_count != rank) return error.UnsupportedStructuralProjectorTerm;
    var young_sum = try youngPermutationIdentity(rank);
    try multiplyYoungRows(shape, rank, &young_sum);
    try multiplyYoungColumns(shape, rank, &young_sum);

    var candidate: BrauerCandidate = .{};
    var term_index: u8 = 0;
    while (term_index < young_sum.count) : (term_index += 1) {
        const term = young_sum.terms[term_index];
        if (term.coefficient.numerator == 0) continue;
        try appendBrauerPermutationWord(&candidate, term.coefficient, term.permutation, rank);
    }
    try uniqueBrauerCandidateWords(&candidate);
    if (candidate.word_count != 0) try out.append(candidate);
}

fn youngPermutationIdentity(rank: u8) !YoungPermutationSum {
    var sum: YoungPermutationSum = .{};
    var permutation = [_]u8{0} ** max_vector_young_boxes;
    var index: u8 = 0;
    while (index < rank) : (index += 1) {
        permutation[index] = index;
    }
    try appendYoungPermutationTerm(&sum, Rational.one(), permutation, rank);
    return sum;
}

fn multiplyYoungRows(shape: YoungShape, rank: u8, sum: *YoungPermutationSum) !void {
    var row_start: u8 = 0;
    var row_index: u8 = 0;
    while (row_index < shape.row_count) : (row_index += 1) {
        const row_len = shape.rows[row_index];
        if (row_len == 0) return error.InvalidYoungShape;
        var boxes = [_]u8{0} ** max_vector_young_boxes;
        var box_index: u8 = 0;
        while (box_index < row_len) : (box_index += 1) {
            boxes[box_index] = row_start + box_index;
        }
        const group = try youngGroupPermutationSum(boxes, row_len, rank, false);
        sum.* = try multiplyYoungPermutationSums(sum.*, group, rank);
        row_start += row_len;
    }
    if (row_start != rank) return error.InvalidYoungShape;
}

fn multiplyYoungColumns(shape: YoungShape, rank: u8, sum: *YoungPermutationSum) !void {
    var column: u8 = 0;
    while (column < shape.rows[0]) : (column += 1) {
        var boxes = [_]u8{0} ** max_vector_young_boxes;
        var count: u8 = 0;
        var row_start: u8 = 0;
        var row_index: u8 = 0;
        while (row_index < shape.row_count) : (row_index += 1) {
            const row_len = shape.rows[row_index];
            if (column < row_len) {
                boxes[count] = row_start + column;
                count += 1;
            }
            row_start += row_len;
        }
        const group = try youngGroupPermutationSum(boxes, count, rank, true);
        sum.* = try multiplyYoungPermutationSums(sum.*, group, rank);
    }
}

fn youngGroupPermutationSum(boxes: [max_vector_young_boxes]u8, count: u8, rank: u8, antisymmetric: bool) !YoungPermutationSum {
    var sum: YoungPermutationSum = .{};
    var used = [_]bool{false} ** max_vector_young_boxes;
    var current = [_]u8{0} ** max_vector_young_boxes;
    try enumerateYoungGroupPermutation(boxes, count, rank, antisymmetric, 0, &used, &current, &sum);
    return sum;
}

fn enumerateYoungGroupPermutation(boxes: [max_vector_young_boxes]u8, count: u8, rank: u8, antisymmetric: bool, depth: u8, used: *[max_vector_young_boxes]bool, current: *[max_vector_young_boxes]u8, sum: *YoungPermutationSum) !void {
    if (depth == count) {
        var permutation = [_]u8{0} ** max_vector_young_boxes;
        var index: u8 = 0;
        while (index < rank) : (index += 1) {
            permutation[index] = index;
        }
        index = 0;
        while (index < count) : (index += 1) {
            permutation[boxes[index]] = current[index];
        }
        const sign: i64 = if (antisymmetric and youngPermutationOdd(current.*, count)) -1 else 1;
        try appendYoungPermutationTerm(sum, try Rational.init(sign, 1), permutation, rank);
        return;
    }

    var source_index: u8 = 0;
    while (source_index < count) : (source_index += 1) {
        if (used[source_index]) continue;
        used[source_index] = true;
        current[depth] = boxes[source_index];
        try enumerateYoungGroupPermutation(boxes, count, rank, antisymmetric, depth + 1, used, current, sum);
        used[source_index] = false;
    }
}

fn youngPermutationOdd(values: [max_vector_young_boxes]u8, count: u8) bool {
    var inversions: u8 = 0;
    var left: u8 = 0;
    while (left < count) : (left += 1) {
        var right = left + 1;
        while (right < count) : (right += 1) {
            if (values[left] > values[right]) inversions += 1;
        }
    }
    return @mod(inversions, 2) != 0;
}

fn multiplyYoungPermutationSums(left: YoungPermutationSum, right: YoungPermutationSum, rank: u8) !YoungPermutationSum {
    var out: YoungPermutationSum = .{};
    var left_index: u8 = 0;
    while (left_index < left.count) : (left_index += 1) {
        var right_index: u8 = 0;
        while (right_index < right.count) : (right_index += 1) {
            const coefficient = try left.terms[left_index].coefficient.mul(right.terms[right_index].coefficient);
            const permutation = composeYoungPermutations(left.terms[left_index].permutation, right.terms[right_index].permutation, rank);
            try appendYoungPermutationTerm(&out, coefficient, permutation, rank);
        }
    }
    return out;
}

fn composeYoungPermutations(left: [max_vector_young_boxes]u8, right: [max_vector_young_boxes]u8, rank: u8) [max_vector_young_boxes]u8 {
    var out = [_]u8{0} ** max_vector_young_boxes;
    var index: u8 = 0;
    while (index < rank) : (index += 1) {
        out[index] = right[left[index]];
    }
    return out;
}

fn appendYoungPermutationTerm(sum: *YoungPermutationSum, coefficient: Rational, permutation: [max_vector_young_boxes]u8, rank: u8) !void {
    if (coefficient.numerator == 0) return;
    var index: u8 = 0;
    while (index < sum.count) : (index += 1) {
        if (!youngPermutationEql(sum.terms[index].permutation, permutation, rank)) continue;
        sum.terms[index].coefficient = try sum.terms[index].coefficient.add(coefficient);
        return;
    }
    if (sum.count == max_young_permutation_terms) return error.UnsupportedTensorBrauerCandidateCap;
    sum.terms[sum.count] = .{ .coefficient = coefficient, .permutation = permutation };
    sum.count += 1;
}

fn youngPermutationEql(left: [max_vector_young_boxes]u8, right: [max_vector_young_boxes]u8, rank: u8) bool {
    var index: u8 = 0;
    while (index < rank) : (index += 1) {
        if (left[index] != right[index]) return false;
    }
    return true;
}

fn appendBrauerPermutationWord(candidate: *BrauerCandidate, coefficient: Rational, permutation: [max_vector_young_boxes]u8, rank: u8) !void {
    var word: BrauerWord = .{ .coefficient = coefficient };
    var slot: u8 = 0;
    while (slot < rank) : (slot += 1) {
        try appendBrauerDeltaEdge(&word, slot, permutation[slot]);
    }
    try candidate.append(word);
}

fn appendVectorYoungTraceCandidates(rank: u8, out: *BrauerCandidateBuffer) !void {
    var left: u8 = 0;
    while (left < rank) : (left += 1) {
        var right = left + 1;
        while (right < rank) : (right += 1) {
            try appendBrauerTraceCandidate(out, rank, left, right);
        }
    }
}

fn appendVectorYoungTraceCandidatesForShape(shape: YoungShape, out: *BrauerCandidateBuffer) !void {
    var left: u8 = 0;
    while (left < shape.box_count) : (left += 1) {
        var right = left + 1;
        while (right < shape.box_count) : (right += 1) {
            if (!youngTracePairAdmissible(shape, left, right)) continue;
            try appendBrauerTraceCandidate(out, shape.box_count, left, right);
        }
    }
}

fn youngTracePairAdmissible(shape: YoungShape, left: u8, right: u8) bool {
    return youngBoxColumn(shape, left) != youngBoxColumn(shape, right);
}

fn youngBoxColumn(shape: YoungShape, box: u8) u8 {
    var row_start: u8 = 0;
    var row: u8 = 0;
    while (row < shape.row_count) : (row += 1) {
        const row_len = shape.rows[row];
        if (box < row_start + row_len) return box - row_start;
        row_start += row_len;
    }
    return std.math.maxInt(u8);
}

fn appendBrauerTraceCandidate(out: *BrauerCandidateBuffer, rank: u8, left: u8, right: u8) !void {
    var word: BrauerWord = .{ .coefficient = Rational.one() };
    try appendBrauerInputTraceEdge(&word, left, right);
    try appendBrauerOutputMetricEdge(&word, left, right);
    var slot: u8 = 0;
    while (slot < rank) : (slot += 1) {
        if (slot != left and slot != right) try appendBrauerDeltaEdge(&word, slot, slot);
    }
    var candidate: BrauerCandidate = .{};
    try candidate.append(word);
    try out.append(candidate);
}

fn appendBrauerDeltaEdge(word: *BrauerWord, input: u8, output: u8) !void {
    if (word.edge_count == max_vector_brauer_edges) return error.UnsupportedTensorPrimitiveTermCap;
    word.edges[word.edge_count] = .{ .kind = .delta, .input_a = input, .output_a = output };
    word.edge_count += 1;
}

fn appendBrauerInputTraceEdge(word: *BrauerWord, left: u8, right: u8) !void {
    if (word.edge_count == max_vector_brauer_edges) return error.UnsupportedTensorPrimitiveTermCap;
    word.edges[word.edge_count] = .{ .kind = .input_trace, .input_a = left, .input_b = right };
    word.edge_count += 1;
}

fn appendBrauerOutputMetricEdge(word: *BrauerWord, left: u8, right: u8) !void {
    if (word.edge_count == max_vector_brauer_edges) return error.UnsupportedTensorPrimitiveTermCap;
    word.edges[word.edge_count] = .{ .kind = .output_metric, .output_a = left, .output_b = right };
    word.edge_count += 1;
}

fn enumerateRawBrauerDiagrams(channel: TensorOnlyChannel, out: *TensorBrauerDiagramBuffer) !void {
    const total = channel.input_slot_count + channel.output_slot_count;
    if (channel.left.slot_count + channel.right.slot_count != channel.input_slot_count) return error.UnsupportedStructuralProjectorTerm;
    if (channel.output.slot_count != channel.output_slot_count) return error.UnsupportedStructuralProjectorTerm;
    if (total > 2 * max_tensor_slots) return error.UnsupportedTensorShapeOverCap;
    if ((total & 1) != 0) return error.UnsupportedStructuralProjectorTerm;

    var diagram: TensorBrauerDiagram = .{ .coefficient = Rational.one() };
    try enumerateRawBrauerDiagramsRec(channel, total, 0, &diagram, out);
    try uniqueTensorBrauerDiagrams(out);
}

fn enumerateRawBrauerDiagramsRec(channel: TensorOnlyChannel, total: u8, used_mask: u32, diagram: *TensorBrauerDiagram, out: *TensorBrauerDiagramBuffer) !void {
    const first = firstUnusedTensorBoundarySlot(total, used_mask) orelse {
        var canonical = diagram.*;
        canonicalizeBrauerWord(&canonical);
        try out.append(canonical);
        return;
    };

    var second = first + 1;
    while (second < total) : (second += 1) {
        if (tensorBoundarySlotUsed(used_mask, second)) continue;
        try pushTensorBrauerBoundaryEdge(channel, diagram, first, second);
        try enumerateRawBrauerDiagramsRec(channel, total, markTensorBoundarySlotUsed(markTensorBoundarySlotUsed(used_mask, first), second), diagram, out);
        diagram.edge_count -= 1;
    }
}

fn firstUnusedTensorBoundarySlot(total: u8, used_mask: u32) ?u8 {
    var slot: u8 = 0;
    while (slot < total) : (slot += 1) {
        if (!tensorBoundarySlotUsed(used_mask, slot)) return slot;
    }
    return null;
}

fn tensorBoundarySlotUsed(used_mask: u32, slot: u8) bool {
    return (used_mask & (@as(u32, 1) << @intCast(slot))) != 0;
}

fn markTensorBoundarySlotUsed(used_mask: u32, slot: u8) u32 {
    return used_mask | (@as(u32, 1) << @intCast(slot));
}

fn pushTensorBrauerBoundaryEdge(channel: TensorOnlyChannel, diagram: *TensorBrauerDiagram, left: u8, right: u8) !void {
    const left_is_input = left < channel.input_slot_count;
    const right_is_input = right < channel.input_slot_count;

    if (left_is_input and right_is_input) {
        try appendBrauerInputTraceEdge(diagram, left, right);
        return;
    }
    if (!left_is_input and !right_is_input) {
        try appendBrauerOutputMetricEdge(diagram, left - channel.input_slot_count, right - channel.input_slot_count);
        return;
    }

    const input = if (left_is_input) left else right;
    const output_boundary = if (left_is_input) right else left;
    try appendBrauerDeltaEdge(diagram, input, output_boundary - channel.input_slot_count);
}

fn uniqueTensorBrauerDiagrams(buffer: *TensorBrauerDiagramBuffer) !void {
    var out: TensorBrauerDiagramBuffer = .{};
    var index: u8 = 0;
    while (index < buffer.count) : (index += 1) {
        var diagram = buffer.diagrams[index];
        diagram.coefficient = Rational.one();
        canonicalizeBrauerWord(&diagram);

        var existing: u8 = 0;
        var found = false;
        while (existing < out.count) : (existing += 1) {
            if (!brauerWordEdgesEql(out.diagrams[existing], diagram)) continue;
            found = true;
            break;
        }
        if (!found) try out.append(diagram);
    }
    buffer.* = out;
}

fn uniqueBrauerCandidateWords(candidate: *BrauerCandidate) !void {
    var out: BrauerCandidate = .{};
    var index: u8 = 0;
    while (index < candidate.word_count) : (index += 1) {
        try appendMergedBrauerWord(&out, candidate.words[index]);
    }
    candidate.* = .{};
    index = 0;
    while (index < out.word_count) : (index += 1) {
        if (out.words[index].coefficient.numerator != 0) try candidate.append(out.words[index]);
    }
}

fn appendMergedBrauerWord(candidate: *BrauerCandidate, input_word: BrauerWord) !void {
    var word = input_word;
    canonicalizeBrauerWord(&word);
    if (word.coefficient.numerator == 0) return;
    var existing: u8 = 0;
    while (existing < candidate.word_count) : (existing += 1) {
        if (!brauerWordEdgesEql(candidate.words[existing], word)) continue;
        candidate.words[existing].coefficient = try candidate.words[existing].coefficient.add(word.coefficient);
        if (candidate.words[existing].coefficient.numerator == 0) {
            var shift = existing;
            while (shift + 1 < candidate.word_count) : (shift += 1) {
                candidate.words[shift] = candidate.words[shift + 1];
            }
            candidate.word_count -= 1;
        }
        return;
    }
    try candidate.append(word);
}

fn uniqueBrauerWords(buffer: *BrauerCandidateBuffer) !void {
    var out: BrauerCandidateBuffer = .{};
    var index: u8 = 0;
    while (index < buffer.count) : (index += 1) {
        var candidate = buffer.candidates[index];
        try uniqueBrauerCandidateWords(&candidate);
        if (candidate.word_count == 0) continue;
        var existing: u8 = 0;
        var merged = false;
        while (existing < out.count) : (existing += 1) {
            if (!brauerCandidateEql(out.candidates[existing], candidate)) continue;
            merged = true;
            break;
        }
        if (!merged) try out.append(candidate);
    }
    buffer.* = .{};
    index = 0;
    while (index < out.count) : (index += 1) {
        try buffer.append(out.candidates[index]);
    }
}

fn brauerCandidateEql(left: BrauerCandidate, right: BrauerCandidate) bool {
    if (left.word_count != right.word_count) return false;
    var index: u8 = 0;
    while (index < left.word_count) : (index += 1) {
        if (!brauerWordEql(left.words[index], right.words[index])) return false;
    }
    return true;
}

fn brauerWordEql(left: BrauerWord, right: BrauerWord) bool {
    return left.coefficient.numerator == right.coefficient.numerator and
        left.coefficient.denominator == right.coefficient.denominator and
        brauerWordEdgesEql(left, right);
}

fn brauerWordEdgesEql(left: BrauerWord, right: BrauerWord) bool {
    if (left.edge_count != right.edge_count) return false;
    var index: u8 = 0;
    while (index < left.edge_count) : (index += 1) {
        const a = left.edges[index];
        const b = right.edges[index];
        if (a.kind != b.kind or a.input_a != b.input_a or a.input_b != b.input_b or a.output_a != b.output_a or a.output_b != b.output_b) return false;
    }
    return true;
}

fn canonicalizeBrauerWord(word: *BrauerWord) void {
    var sorted = false;
    while (!sorted) {
        sorted = true;
        var index: u8 = 1;
        while (index < word.edge_count) : (index += 1) {
            if (!brauerEdgeLess(word.edges[index], word.edges[index - 1])) continue;
            const temporary = word.edges[index - 1];
            word.edges[index - 1] = word.edges[index];
            word.edges[index] = temporary;
            sorted = false;
        }
    }
}

fn brauerEdgeLess(left: BrauerEdge, right: BrauerEdge) bool {
    if (@intFromEnum(left.kind) != @intFromEnum(right.kind)) return @intFromEnum(left.kind) < @intFromEnum(right.kind);
    if (left.input_a != right.input_a) return left.input_a < right.input_a;
    if (left.input_b != right.input_b) return left.input_b < right.input_b;
    if (left.output_a != right.output_a) return left.output_a < right.output_a;
    return left.output_b < right.output_b;
}

fn compileVectorBrauerGram(program: *VectorBrauerProgram, candidates: BrauerCandidateBuffer, rank: u8, dimension: u16) !void {
    var gram: [max_vector_brauer_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_vector_brauer_gram_entries;
    var row: usize = 0;
    while (row < candidates.count) : (row += 1) {
        var column: usize = 0;
        while (column <= row) : (column += 1) {
            const value = try brauerCandidateInnerProduct(dimension, rank, candidates.candidates[row], candidates.candidates[column]);
            gram[row * candidates.count + column] = value;
            gram[column * candidates.count + row] = value;
        }
    }

    const pivots = try selectVectorBrauerGramPivots(candidates.count, gram[0..]);
    if (pivots.count == 0) return error.SingularGramMatrix;
    var pivot_gram: [max_vector_brauer_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_vector_brauer_gram_entries;
    row = 0;
    while (row < pivots.count) : (row += 1) {
        var column: usize = 0;
        while (column < pivots.count) : (column += 1) {
            pivot_gram[row * pivots.count + column] = gram[@as(usize, pivots.pivots[row]) * candidates.count + pivots.pivots[column]];
        }
    }

    program.candidate_count = candidates.count;
    program.pivot_count = pivots.count;
    program.candidates = candidates.candidates;
    var pivot_index: u8 = 0;
    while (pivot_index < pivots.count) : (pivot_index += 1) {
        program.pivots[pivot_index] = pivots.pivots[pivot_index];
    }
    program.inverse_gram = try invertVectorBrauerGram(pivots.count, pivot_gram[0..]);
}

fn brauerCandidateInnerProduct(dimension: u16, rank: u8, left: BrauerCandidate, right: BrauerCandidate) !Rational {
    var acc = Rational.zero();
    var left_index: u8 = 0;
    while (left_index < left.word_count) : (left_index += 1) {
        var right_index: u8 = 0;
        while (right_index < right.word_count) : (right_index += 1) {
            acc = try acc.add(try brauerInnerProduct(dimension, rank, left.words[left_index], right.words[right_index]));
        }
    }
    return acc;
}

fn composeBrauerCandidates(rank: u8, dimension: u16, left: BrauerCandidate, right: BrauerCandidate) !BrauerCandidate {
    var out: BrauerCandidate = .{};
    var left_index: u8 = 0;
    while (left_index < left.word_count) : (left_index += 1) {
        var right_index: u8 = 0;
        while (right_index < right.word_count) : (right_index += 1) {
            const word = try composeBrauerWords(rank, dimension, left.words[left_index], right.words[right_index]);
            try appendMergedBrauerWord(&out, word);
        }
    }
    return out;
}

fn composeBrauerWords(rank: u8, dimension: u16, left: BrauerWord, right: BrauerWord) !BrauerWord {
    var graph: BrauerContraction = .{};
    graph.init(rank);
    try graph.addCompositionLeftWord(rank, left);
    try graph.addCompositionRightWord(rank, right);

    var out: BrauerWord = .{ .coefficient = try left.coefficient.mul(right.coefficient) };
    const loops = try appendComposedBrauerWordEdges(&out, &graph, rank);
    out.coefficient = try out.coefficient.mul(try powRational(dimension, loops));
    canonicalizeBrauerWord(&out);
    return out;
}

fn normalizedBrauerIdempotentCandidate(rank: u8, dimension: u16, candidate: BrauerCandidate) !BrauerCandidate {
    const square = try composeBrauerCandidates(rank, dimension, candidate, candidate);
    const scale = try brauerCandidateProportionalScale(candidate, square);
    return try scaleBrauerCandidate(candidate, try Rational.one().div(scale));
}

fn scaleBrauerCandidate(candidate: BrauerCandidate, scale: Rational) !BrauerCandidate {
    var out: BrauerCandidate = .{};
    var word_index: u8 = 0;
    while (word_index < candidate.word_count) : (word_index += 1) {
        var word = candidate.words[word_index];
        word.coefficient = try word.coefficient.mul(scale);
        try appendMergedBrauerWord(&out, word);
    }
    return out;
}

fn traceFreeBrauerProjectorCandidate(rank: u8, dimension: u16, young_candidate: BrauerCandidate) !BrauerCandidate {
    const allocator = std.heap.page_allocator;
    const trace_generators = try allocator.create(BrauerCandidateBuffer);
    defer allocator.destroy(trace_generators);
    trace_generators.* = .{};
    try appendVectorYoungTraceCandidates(rank, trace_generators);
    return traceFreeBrauerProjectorCandidateWithTraces(rank, dimension, young_candidate, trace_generators);
}

fn traceFreeBrauerProjectorCandidateForShape(shape: YoungShape, dimension: u16, young_candidate: BrauerCandidate) !BrauerCandidate {
    const allocator = std.heap.page_allocator;
    const trace_generators = try allocator.create(BrauerCandidateBuffer);
    defer allocator.destroy(trace_generators);
    trace_generators.* = .{};
    try appendVectorYoungTraceCandidatesForShape(shape, trace_generators);
    return traceFreeBrauerProjectorCandidateWithTraces(shape.box_count, dimension, young_candidate, trace_generators);
}

fn traceFreeBrauerProjectorBasisForShape(shape: YoungShape, dimension: u16, young_candidate: BrauerCandidate) !TraceFreeBrauerProjector {
    const allocator = std.heap.page_allocator;
    const trace_generators = try allocator.create(BrauerCandidateBuffer);
    defer allocator.destroy(trace_generators);
    trace_generators.* = .{};
    try appendVectorYoungTraceCandidatesForShape(shape, trace_generators);
    return traceFreeBrauerProjectorBasisWithTraces(shape.box_count, dimension, young_candidate, trace_generators);
}

fn traceFreeBrauerProjectorCandidateWithTraces(rank: u8, dimension: u16, young_candidate: BrauerCandidate, trace_generators: *const BrauerCandidateBuffer) !BrauerCandidate {
    var projector = try traceFreeBrauerProjectorBasisWithTraces(rank, dimension, young_candidate, trace_generators);
    defer projector.deinit();
    return materializeTraceFreeBrauerProjector(projector);
}

fn traceFreeBrauerProjectorBasisWithTraces(rank: u8, dimension: u16, young_candidate: BrauerCandidate, trace_generators: *const BrauerCandidateBuffer) !TraceFreeBrauerProjector {
    const young_idempotent = try normalizedBrauerIdempotentCandidate(rank, dimension, young_candidate);
    if (trace_generators.count == 0) return traceFreeBrauerProjectorFromSingleCandidate(young_idempotent);

    const allocator = std.heap.page_allocator;
    const basis = try allocator.create(BrauerCandidateBuffer);
    defer allocator.destroy(basis);
    basis.* = .{};
    var paths: TraceRemovalPathBuffer = .{};
    try buildTraceClosureBasis(rank, dimension, young_idempotent, trace_generators, basis, &paths);
    if (basis.count == 0) return error.UnsupportedStructuralProjectorTerm;
    if (basis.count == 1) return traceFreeBrauerProjectorFromSingleCandidate(basis.candidates[0]);
    if (paths.count != basis.count) return error.UnsupportedStructuralProjectorTerm;

    const solution = try solveTraceRemovalCoefficients(rank, dimension, basis, trace_generators);
    var projector = try allocTraceFreeBrauerProjector(basis.count);
    @memcpy(projector.basis[0..basis.count], basis.candidates[0..basis.count]);
    @memcpy(projector.paths[0..basis.count], paths.paths[0..basis.count]);
    projector.coefficients[0] = Rational.one();
    var basis_index: u8 = 1;
    while (basis_index < basis.count) : (basis_index += 1) {
        projector.coefficients[basis_index] = solution[basis_index - 1];
    }
    return projector;
}

fn traceFreeBrauerProjectorFromSingleCandidate(candidate: BrauerCandidate) !TraceFreeBrauerProjector {
    var projector = try allocTraceFreeBrauerProjector(1);
    projector.basis[0] = candidate;
    projector.coefficients[0] = Rational.one();
    projector.paths[0] = .{};
    return projector;
}

fn allocTraceFreeBrauerProjector(basis_count: u8) !TraceFreeBrauerProjector {
    if (basis_count == 0) return error.UnsupportedStructuralProjectorTerm;
    const allocator = std.heap.page_allocator;
    const basis = try allocator.alloc(BrauerCandidate, basis_count);
    errdefer allocator.free(basis);
    const coefficients = try allocator.alloc(Rational, basis_count);
    errdefer allocator.free(coefficients);
    const paths = try allocator.alloc(TraceRemovalPath, basis_count);
    errdefer allocator.free(paths);
    @memset(coefficients, Rational.zero());
    @memset(paths, .{});
    return .{
        .basis_count = basis_count,
        .basis = basis,
        .coefficients = coefficients,
        .paths = paths,
    };
}

fn materializeTraceFreeBrauerProjector(projector: TraceFreeBrauerProjector) !BrauerCandidate {
    if (projector.basis_count == 0) return error.UnsupportedStructuralProjectorTerm;
    var out: BrauerCandidate = .{};
    var basis_index: u8 = 0;
    while (basis_index < projector.basis_count) : (basis_index += 1) {
        const coefficient = projector.coefficients[basis_index];
        if (coefficient.numerator == 0) continue;
        const scaled = try scaleBrauerCandidate(projector.basis[basis_index], coefficient);
        var word_index: u8 = 0;
        while (word_index < scaled.word_count) : (word_index += 1) {
            try appendMergedBrauerWord(&out, scaled.words[word_index]);
        }
    }
    return out;
}

fn buildTraceClosureBasis(rank: u8, dimension: u16, young_idempotent: BrauerCandidate, trace_generators: *const BrauerCandidateBuffer, basis: *BrauerCandidateBuffer, paths: *TraceRemovalPathBuffer) !void {
    try appendBrauerBasisCandidateWithPath(basis, paths, young_idempotent, .{});
    var basis_index: u8 = 0;
    while (basis_index < basis.count) : (basis_index += 1) {
        var trace_index: u8 = 0;
        while (trace_index < trace_generators.count) : (trace_index += 1) {
            const product = try composeBrauerCandidates(rank, dimension, trace_generators.candidates[trace_index], basis.candidates[basis_index]);
            var path = paths.paths[basis_index];
            try appendTraceRemovalPathStep(&path, trace_index);
            try appendBrauerBasisCandidateWithPath(basis, paths, product, path);
        }
    }
}

fn appendTraceRemovalPathStep(path: *TraceRemovalPath, trace_index: u8) !void {
    if (path.trace_count == max_tensor_trace_path_steps) return error.ProjectorProgramTooLarge;
    path.trace_indices[path.trace_count] = trace_index;
    path.trace_count += 1;
}

fn appendBrauerBasisCandidateWithPath(basis: *BrauerCandidateBuffer, paths: *TraceRemovalPathBuffer, candidate: BrauerCandidate, path: TraceRemovalPath) !void {
    if (candidate.word_count == 0) return;
    var index: u8 = 0;
    while (index < basis.count) : (index += 1) {
        _ = brauerCandidateProportionalScale(basis.candidates[index], candidate) catch continue;
        return;
    }
    if (try brauerCandidateInBasisSpan(basis, &candidate)) return;
    try basis.append(candidate);
    try paths.append(path);
}

fn appendBrauerBasisCandidate(basis: *BrauerCandidateBuffer, candidate: BrauerCandidate) !void {
    if (candidate.word_count == 0) return;
    var index: u8 = 0;
    while (index < basis.count) : (index += 1) {
        _ = brauerCandidateProportionalScale(basis.candidates[index], candidate) catch {
            index += 1;
            continue;
        };
        return;
    }
    if (try brauerCandidateInBasisSpan(basis, &candidate)) return;
    try basis.append(candidate);
}

fn brauerCandidateInBasisSpan(basis: *const BrauerCandidateBuffer, candidate: *const BrauerCandidate) !bool {
    if (basis.count == 0) return false;
    return brauerCandidateInNonemptyBasisSpan(basis, candidate);
}

fn brauerCandidateInNonemptyBasisSpan(basis: *const BrauerCandidateBuffer, candidate: *const BrauerCandidate) !bool {
    const allocator = std.heap.page_allocator;
    const system = try allocator.create(BrauerEquationSystem);
    defer allocator.destroy(system);
    system.* = .{ .column_count = basis.count };
    var basis_index: u8 = 0;
    while (basis_index < basis.count) : (basis_index += 1) {
        try addTraceEquationCandidate(system, 0, basis.candidates[basis_index], basis_index, Rational.one());
    }
    try addTraceEquationCandidate(system, 0, candidate.*, system.column_count, Rational.one());
    _ = solveBrauerEquationSystem(system) catch |err| switch (err) {
        error.UnsupportedStructuralProjectorTerm => return false,
        else => return err,
    };
    return true;
}

fn solveTraceRemovalCoefficients(rank: u8, dimension: u16, basis: *const BrauerCandidateBuffer, trace_generators: *const BrauerCandidateBuffer) ![max_vector_brauer_candidates]Rational {
    const allocator = std.heap.page_allocator;
    const system = try allocator.create(BrauerEquationSystem);
    defer allocator.destroy(system);
    system.* = .{ .column_count = basis.count - 1 };
    var trace_index: u8 = 0;
    while (trace_index < trace_generators.count) : (trace_index += 1) {
        const target = try composeBrauerCandidates(rank, dimension, trace_generators.candidates[trace_index], basis.candidates[0]);
        try addTraceEquationCandidate(system, trace_index, target, system.column_count, try Rational.init(-1, 1));

        var basis_index: u8 = 1;
        while (basis_index < basis.count) : (basis_index += 1) {
            const image = try composeBrauerCandidates(rank, dimension, trace_generators.candidates[trace_index], basis.candidates[basis_index]);
            try addTraceEquationCandidate(system, trace_index, image, basis_index - 1, Rational.one());
        }
    }
    return solveBrauerEquationSystem(system);
}

fn addTraceEquationCandidate(system: *BrauerEquationSystem, trace_index: u8, candidate: BrauerCandidate, column: u8, scale: Rational) !void {
    var word_index: u8 = 0;
    while (word_index < candidate.word_count) : (word_index += 1) {
        const row = try traceEquationRow(system, trace_index, candidate.words[word_index]);
        const entry_index = @as(usize, row) * (@as(usize, system.column_count) + 1) + column;
        system.entries[entry_index] = try system.entries[entry_index].add(try candidate.words[word_index].coefficient.mul(scale));
    }
}

fn traceEquationRow(system: *BrauerEquationSystem, trace_index: u8, word: BrauerWord) !u16 {
    var canonical = word;
    canonical.coefficient = Rational.one();
    canonicalizeBrauerWord(&canonical);
    var row: u16 = 0;
    while (row < system.row_count) : (row += 1) {
        const key = system.keys[row];
        if (key.trace_index == trace_index and brauerWordEdgesEql(key.word, canonical)) return row;
    }
    if (system.row_count == max_vector_brauer_gram_entries) return error.UnsupportedTensorBrauerCandidateCap;
    system.keys[system.row_count] = .{ .trace_index = trace_index, .word = canonical };
    system.row_count += 1;
    return system.row_count - 1;
}

fn solveBrauerEquationSystem(system: *BrauerEquationSystem) ![max_vector_brauer_candidates]Rational {
    var solution = [_]Rational{Rational.zero()} ** max_vector_brauer_candidates;
    const width: usize = system.column_count;
    const stride = width + 1;
    var pivot_columns = [_]u8{0} ** max_vector_brauer_candidates;
    var pivot_count: u8 = 0;
    var pivot_row: usize = 0;

    var column: usize = 0;
    while (column < width and pivot_row < system.row_count) : (column += 1) {
        const source_row = findBrauerEquationPivotRow(system, pivot_row, column) orelse continue;
        if (source_row != pivot_row) swapBrauerEquationRows(system, pivot_row, source_row);
        const pivot = system.entries[pivot_row * stride + column];
        var scale_column = column;
        while (scale_column < stride) : (scale_column += 1) {
            system.entries[pivot_row * stride + scale_column] = try system.entries[pivot_row * stride + scale_column].div(pivot);
        }

        var row: usize = 0;
        while (row < system.row_count) : (row += 1) {
            if (row == pivot_row) continue;
            const factor = system.entries[row * stride + column];
            if (factor.numerator == 0) continue;
            scale_column = column;
            while (scale_column < stride) : (scale_column += 1) {
                const scaled = try factor.mul(system.entries[pivot_row * stride + scale_column]);
                system.entries[row * stride + scale_column] = try system.entries[row * stride + scale_column].sub(scaled);
            }
        }

        pivot_columns[pivot_count] = @intCast(column);
        pivot_count += 1;
        pivot_row += 1;
    }

    var row: usize = 0;
    while (row < system.row_count) : (row += 1) {
        var has_coefficient = false;
        column = 0;
        while (column < width) : (column += 1) {
            if (system.entries[row * stride + column].numerator != 0) has_coefficient = true;
        }
        if (!has_coefficient and system.entries[row * stride + width].numerator != 0) return error.UnsupportedStructuralProjectorTerm;
    }

    var pivot_index: u8 = 0;
    while (pivot_index < pivot_count) : (pivot_index += 1) {
        solution[pivot_columns[pivot_index]] = system.entries[@as(usize, pivot_index) * stride + width];
    }
    return solution;
}

fn findBrauerEquationPivotRow(system: *const BrauerEquationSystem, first_row: usize, column: usize) ?usize {
    const stride = @as(usize, system.column_count) + 1;
    var row = first_row;
    while (row < system.row_count) : (row += 1) {
        if (system.entries[row * stride + column].numerator != 0) return row;
    }
    return null;
}

fn swapBrauerEquationRows(system: *BrauerEquationSystem, left: usize, right: usize) void {
    const stride = @as(usize, system.column_count) + 1;
    var column: usize = 0;
    while (column < stride) : (column += 1) {
        const left_index = left * stride + column;
        const right_index = right * stride + column;
        const temporary = system.entries[left_index];
        system.entries[left_index] = system.entries[right_index];
        system.entries[right_index] = temporary;
    }
}

fn assertTraceFreeBrauerCandidate(rank: u8, dimension: u16, candidate: BrauerCandidate, trace_generators: BrauerCandidateBuffer) !void {
    var trace_index: u8 = 0;
    while (trace_index < trace_generators.count) : (trace_index += 1) {
        const traced = try composeBrauerCandidates(rank, dimension, trace_generators.candidates[trace_index], candidate);
        if (traced.word_count != 0) return error.UnsupportedStructuralProjectorTerm;
    }
}

fn appendComposedBrauerWordEdges(word: *BrauerWord, graph: *BrauerContraction, rank: u8) !u8 {
    var loops: u8 = 0;
    var root: u8 = 0;
    while (root < 3 * rank) : (root += 1) {
        if (graph.find(root) != root) continue;
        var source_count: u8 = 0;
        var output_count: u8 = 0;
        var first_source: u8 = 0;
        var second_source: u8 = 0;
        var first_output: u8 = 0;
        var second_output: u8 = 0;

        var slot: u8 = 0;
        while (slot < rank) : (slot += 1) {
            if (graph.find(slot) == root) {
                if (source_count == 0) first_source = slot else if (source_count == 1) second_source = slot;
                source_count += 1;
            }
            if (graph.find(2 * rank + slot) == root) {
                if (output_count == 0) first_output = slot else if (output_count == 1) second_output = slot;
                output_count += 1;
            }
        }

        if (source_count == 0 and output_count == 0) {
            loops += 1;
        } else if (source_count == 1 and output_count == 1) {
            try appendBrauerDeltaEdge(word, first_source, first_output);
        } else if (source_count == 2 and output_count == 0) {
            try appendBrauerInputTraceEdge(word, first_source, second_source);
        } else if (source_count == 0 and output_count == 2) {
            try appendBrauerOutputMetricEdge(word, first_output, second_output);
        } else {
            return error.UnsupportedStructuralProjectorTerm;
        }
    }
    return loops;
}

fn brauerCandidateProportionalScale(base: BrauerCandidate, product: BrauerCandidate) !Rational {
    var scale = Rational.zero();
    var has_scale = false;
    var base_index: u8 = 0;
    while (base_index < base.word_count) : (base_index += 1) {
        const base_word = base.words[base_index];
        if (base_word.coefficient.numerator == 0) continue;
        var product_index: u8 = 0;
        var found = false;
        while (product_index < product.word_count) : (product_index += 1) {
            const product_word = product.words[product_index];
            if (!brauerWordEdgesEql(base_word, product_word)) continue;
            const ratio = try product_word.coefficient.div(base_word.coefficient);
            if (!has_scale) {
                scale = ratio;
                has_scale = true;
            } else if (scale.numerator != ratio.numerator or scale.denominator != ratio.denominator) {
                return error.UnsupportedStructuralProjectorTerm;
            }
            found = true;
            break;
        }
        if (!found) return error.UnsupportedStructuralProjectorTerm;
    }
    if (!has_scale) return error.SingularGramMatrix;

    var product_index: u8 = 0;
    while (product_index < product.word_count) : (product_index += 1) {
        var base_match = false;
        base_index = 0;
        while (base_index < base.word_count) : (base_index += 1) {
            if (brauerWordEdgesEql(base.words[base_index], product.words[product_index])) {
                base_match = true;
                break;
            }
        }
        if (!base_match and product.words[product_index].coefficient.numerator != 0) return error.UnsupportedStructuralProjectorTerm;
    }
    return scale;
}

fn vectorBrauerProgramTermCount(program: VectorBrauerProgram) !u8 {
    var count: u16 = 0;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            if (program.inverse_gram[@as(usize, row) * program.pivot_count + column].numerator != 0) count += 1;
        }
    }
    if (count > std.math.maxInt(u8)) return error.ProjectorProgramTooLarge;
    return @intCast(count);
}

fn vectorBrauerProgramTermAt(program: VectorBrauerProgram, term_index: u8) !VectorBrauerProgramTerm {
    var seen: u8 = 0;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
            if (coefficient.numerator == 0) continue;
            const left_candidate = program.pivots[row];
            const right_candidate = program.pivots[column];
            if (seen == term_index) {
                return .{
                    .left_candidate = left_candidate,
                    .right_candidate = right_candidate,
                    .coefficient = coefficient,
                };
            }
            seen += 1;
        }
    }
    return error.ProjectorConstructorTermOutOfBounds;
}

fn appendGramDerivedVectorBrauerTerms(program: *VectorBrauerProgram, spec: VectorSlotProjectorSpec) !void {
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
            if (coefficient.numerator == 0) continue;
            const left_candidate = program.pivots[row];
            const right_candidate = program.pivots[column];
            try appendMaterializedVectorBrauerPairTerms(program, spec, program.*, left_candidate, right_candidate, coefficient);
        }
    }
}

fn materializeVectorBrauerProgramTerm(spec: VectorSlotProjectorSpec, program: VectorBrauerProgram, term_index: u8) !VectorBrauerTerm {
    const program_term = try vectorBrauerProgramTermAt(program, term_index);
    var out: VectorBrauerProgram = .{};
    try appendMaterializedVectorBrauerPairTerms(&out, spec, program, program_term.left_candidate, program_term.right_candidate, program_term.coefficient);
    if (out.term_count != 1) return error.UnsupportedStructuralProjectorTerm;
    return out.terms[0];
}

fn appendMaterializedVectorBrauerPairTerms(out: *VectorBrauerProgram, spec: VectorSlotProjectorSpec, program: VectorBrauerProgram, left_candidate: u8, right_candidate: u8, coefficient: Rational) !void {
    const left = program.candidates[left_candidate];
    const right = program.candidates[right_candidate];
    var left_word_index: u8 = 0;
    while (left_word_index < left.word_count) : (left_word_index += 1) {
        var right_word_index: u8 = 0;
        while (right_word_index < right.word_count) : (right_word_index += 1) {
            var word_coefficient = try coefficient.mul(left.words[left_word_index].coefficient);
            word_coefficient = try word_coefficient.mul(right.words[right_word_index].coefficient);
            if (word_coefficient.numerator == 0) continue;
            const term = try materializeVectorBrauerWordPairTerm(spec, left.words[left_word_index], right.words[right_word_index], word_coefficient);
            try appendMergedVectorBrauerTerm(out, term);
        }
    }
}

fn appendMaterializedTensorContractionPairTerms(out: *VectorBrauerProgram, spec: VectorSlotProjectorSpec, program: VectorBrauerProgram, left_candidate: u8, right_candidate: u8, coefficient: Rational) !void {
    const left = program.candidates[left_candidate];
    const right = program.candidates[right_candidate];
    var left_word_index: u8 = 0;
    while (left_word_index < left.word_count) : (left_word_index += 1) {
        var right_word_index: u8 = 0;
        while (right_word_index < right.word_count) : (right_word_index += 1) {
            var word_coefficient = try coefficient.mul(left.words[left_word_index].coefficient);
            word_coefficient = try word_coefficient.mul(right.words[right_word_index].coefficient);
            if (word_coefficient.numerator == 0) continue;
            const term = try materializeTensorContractionWordPairTerm(spec, left.words[left_word_index], right.words[right_word_index], word_coefficient);
            try appendMergedVectorBrauerTerm(out, term);
        }
    }
}

fn materializeVectorBrauerWordPairTerm(spec: VectorSlotProjectorSpec, left_word: BrauerWord, right_word: BrauerWord, coefficient: Rational) !VectorBrauerTerm {
    var term = try vectorBrauerTerm(coefficient);
    try appendVectorBrauerWordTermAtoms(&term, spec, left_word, false);
    try appendVectorBrauerWordTermAtoms(&term, spec, right_word, true);
    canonicalizeVectorBrauerTerm(&term);
    return term;
}

fn materializeTensorContractionWordPairTerm(spec: VectorSlotProjectorSpec, left_word: BrauerWord, right_word: BrauerWord, coefficient: Rational) !VectorBrauerTerm {
    var term = try vectorBrauerTerm(coefficient);
    try appendVectorBrauerWordTermAtoms(&term, spec, left_word, false);
    try appendVectorBrauerWordTermAtoms(&term, spec, right_word, false);
    canonicalizeVectorBrauerTerm(&term);
    return term;
}

fn appendVectorBrauerWordTermAtoms(term: *VectorBrauerTerm, spec: VectorSlotProjectorSpec, word: BrauerWord, adjoint: bool) !void {
    var edge_index: u8 = 0;
    while (edge_index < word.edge_count) : (edge_index += 1) {
        const edge = word.edges[edge_index];
        switch (edge.kind) {
            .delta => try vectorBrauerTermDeltaFromSlots(term, spec, edge.input_a, edge.output_a),
            .input_trace => if (adjoint)
                try vectorBrauerTermOutputMetric(term, spec, edge.input_a, edge.input_b)
            else
                try vectorBrauerTermInputMetric(term, spec, edge.input_a, edge.input_b),
            .output_metric => if (adjoint)
                try vectorBrauerTermInputMetric(term, spec, edge.output_a, edge.output_b)
            else
                try vectorBrauerTermOutputMetric(term, spec, edge.output_a, edge.output_b),
        }
    }
}

fn appendMergedVectorBrauerTerm(program: *VectorBrauerProgram, term: VectorBrauerTerm) !void {
    if (term.coefficient.numerator == 0) return;
    var index: u8 = 0;
    while (index < program.term_count) : (index += 1) {
        if (!vectorBrauerTermAtomsEql(program.terms[index], term)) continue;
        program.terms[index].coefficient = try program.terms[index].coefficient.add(term.coefficient);
        if (program.terms[index].coefficient.numerator == 0) {
            var shift = index;
            while (shift + 1 < program.term_count) : (shift += 1) {
                program.terms[shift] = program.terms[shift + 1];
            }
            program.term_count -= 1;
        }
        return;
    }
    try appendVectorBrauerTerm(program, term);
}

fn vectorBrauerTermAtomsEql(left: VectorBrauerTerm, right: VectorBrauerTerm) bool {
    if (left.atom_count != right.atom_count) return false;
    var index: u8 = 0;
    while (index < left.atom_count) : (index += 1) {
        const a = left.atoms[index];
        const b = right.atoms[index];
        if (a.kind != b.kind or
            a.upper != b.upper or
            a.upper_slot != b.upper_slot or
            a.lower != b.lower or
            a.lower_slot != b.lower_slot or
            a.left != b.left or
            a.left_slot != b.left_slot or
            a.right != b.right or
            a.right_slot != b.right_slot or
            a.hodge_input != b.hodge_input or
            a.hodge_output != b.hodge_output) return false;
    }
    return true;
}

fn canonicalizeVectorBrauerTerm(term: *VectorBrauerTerm) void {
    var index: u8 = 0;
    while (index < term.atom_count) : (index += 1) {
        if (term.atoms[index].kind == .metric and vectorBrauerEndpointLess(term.atoms[index].right, term.atoms[index].right_slot, term.atoms[index].left, term.atoms[index].left_slot)) {
            const left = term.atoms[index].left;
            const left_slot = term.atoms[index].left_slot;
            term.atoms[index].left = term.atoms[index].right;
            term.atoms[index].left_slot = term.atoms[index].right_slot;
            term.atoms[index].right = left;
            term.atoms[index].right_slot = left_slot;
        }
    }

    var sorted = false;
    while (!sorted) {
        sorted = true;
        index = 1;
        while (index < term.atom_count) : (index += 1) {
            if (!vectorBrauerAtomLess(term.atoms[index], term.atoms[index - 1])) continue;
            const temporary = term.atoms[index - 1];
            term.atoms[index - 1] = term.atoms[index];
            term.atoms[index] = temporary;
            sorted = false;
        }
    }
}

fn vectorBrauerEndpointLess(left_block: rendering.IndexBlockId, left_slot: u8, right_block: rendering.IndexBlockId, right_slot: u8) bool {
    return left_block < right_block or (left_block == right_block and left_slot < right_slot);
}

fn vectorBrauerAtomLess(left: VectorBrauerAtom, right: VectorBrauerAtom) bool {
    if (@intFromEnum(left.kind) != @intFromEnum(right.kind)) return @intFromEnum(left.kind) < @intFromEnum(right.kind);
    if (left.upper != right.upper) return left.upper < right.upper;
    if (left.upper_slot != right.upper_slot) return left.upper_slot < right.upper_slot;
    if (left.lower != right.lower) return left.lower < right.lower;
    if (left.lower_slot != right.lower_slot) return left.lower_slot < right.lower_slot;
    if (left.left != right.left) return left.left < right.left;
    if (left.left_slot != right.left_slot) return left.left_slot < right.left_slot;
    if (left.right != right.right) return left.right < right.right;
    if (left.right_slot != right.right_slot) return left.right_slot < right.right_slot;
    if (left.hodge_input != right.hodge_input) return left.hodge_input < right.hodge_input;
    return left.hodge_output < right.hodge_output;
}

fn appendComposedVectorBrauerTermAtoms(term: *VectorBrauerTerm, spec: VectorSlotProjectorSpec, graph: *BrauerContraction, rank: u8) !u8 {
    var loops: u8 = 0;
    var root: u8 = 0;
    while (root < 3 * rank) : (root += 1) {
        if (graph.find(root) != root) continue;
        var source_count: u8 = 0;
        var output_count: u8 = 0;
        var first_source: u8 = 0;
        var second_source: u8 = 0;
        var first_output: u8 = 0;
        var second_output: u8 = 0;

        var slot: u8 = 0;
        while (slot < rank) : (slot += 1) {
            if (graph.find(slot) == root) {
                if (source_count == 0) first_source = slot else if (source_count == 1) second_source = slot;
                source_count += 1;
            }
            if (graph.find(2 * rank + slot) == root) {
                if (output_count == 0) first_output = slot else if (output_count == 1) second_output = slot;
                output_count += 1;
            }
        }

        if (source_count == 0 and output_count == 0) {
            loops += 1;
        } else if (source_count == 1 and output_count == 1) {
            try vectorBrauerTermDeltaFromSlots(term, spec, first_source, first_output);
        } else if (source_count == 2 and output_count == 0) {
            try vectorBrauerTermInputMetric(term, spec, first_source, second_source);
        } else if (source_count == 0 and output_count == 2) {
            try vectorBrauerTermOutputMetric(term, spec, first_output, second_output);
        } else {
            return error.UnsupportedStructuralProjectorTerm;
        }
    }
    return loops;
}

fn vectorBrauerTermDeltaFromSlots(term: *VectorBrauerTerm, spec: VectorSlotProjectorSpec, input: u8, output: u8) !void {
    const source = try vectorSlotSource(spec, input);
    const target = try vectorSlotTarget(spec, output);
    try vectorBrauerTermDelta(term, source.block, source.slot, target.block, target.slot);
}

fn vectorBrauerTermInputMetric(term: *VectorBrauerTerm, spec: VectorSlotProjectorSpec, left: u8, right: u8) !void {
    const left_source = try vectorSlotSource(spec, left);
    const right_source = try vectorSlotSource(spec, right);
    try vectorBrauerTermMetric(term, left_source.block, left_source.slot, right_source.block, right_source.slot);
}

fn vectorBrauerTermOutputMetric(term: *VectorBrauerTerm, spec: VectorSlotProjectorSpec, left: u8, right: u8) !void {
    const left_target = try vectorSlotTarget(spec, left);
    const right_target = try vectorSlotTarget(spec, right);
    try vectorBrauerTermMetric(term, left_target.block, left_target.slot, right_target.block, right_target.slot);
}

fn appendVectorBrauerWordAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: VectorSlotProjectorSpec, word: BrauerWord) !void {
    var edge_index: u8 = 0;
    while (edge_index < word.edge_count) : (edge_index += 1) {
        const edge = word.edges[edge_index];
        switch (edge.kind) {
            .delta => try appendVectorSlotDeltaAtom(allocator, atoms, spec, edge.input_a, edge.output_a),
            .input_trace => try appendVectorSlotInputMetricAtom(allocator, atoms, spec, edge.input_a, edge.input_b),
            .output_metric => try appendVectorSlotOutputMetricAtom(allocator, atoms, spec, edge.output_a, edge.output_b),
        }
    }
}

fn appendVectorBrauerWordAdjointAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: VectorSlotProjectorSpec, word: BrauerWord) !void {
    var edge_index: u8 = 0;
    while (edge_index < word.edge_count) : (edge_index += 1) {
        const edge = word.edges[edge_index];
        switch (edge.kind) {
            .delta => try appendVectorSlotDeltaAtom(allocator, atoms, spec, edge.input_a, edge.output_a),
            .input_trace => try appendVectorSlotOutputMetricAtom(allocator, atoms, spec, edge.input_a, edge.input_b),
            .output_metric => try appendVectorSlotInputMetricAtom(allocator, atoms, spec, edge.output_a, edge.output_b),
        }
    }
}

fn appendVectorSlotDeltaAtom(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: VectorSlotProjectorSpec, input: u8, output: u8) !void {
    const source = try vectorSlotSource(spec, input);
    const target = try vectorSlotTarget(spec, output);
    try atoms.append(allocator, .{ .vector_slot_delta = .{
        .upper = source.block,
        .upper_slot = source.slot,
        .lower = target.block,
        .lower_slot = target.slot,
    } });
}

fn appendVectorSlotInputMetricAtom(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: VectorSlotProjectorSpec, left: u8, right: u8) !void {
    const left_source = try vectorSlotSource(spec, left);
    const right_source = try vectorSlotSource(spec, right);
    try atoms.append(allocator, .{ .vector_slot_metric = .{
        .left = left_source.block,
        .left_slot = left_source.slot,
        .right = right_source.block,
        .right_slot = right_source.slot,
    } });
}

fn appendVectorSlotOutputMetricAtom(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: VectorSlotProjectorSpec, left: u8, right: u8) !void {
    const left_target = try vectorSlotTarget(spec, left);
    const right_target = try vectorSlotTarget(spec, right);
    try atoms.append(allocator, .{ .vector_slot_metric = .{
        .left = left_target.block,
        .left_slot = left_target.slot,
        .right = right_target.block,
        .right_slot = right_target.slot,
    } });
}

const VectorSlotSource = struct {
    block: rendering.IndexBlockId,
    slot: u8,
};

fn vectorSlotSource(spec: VectorSlotProjectorSpec, input: u8) !VectorSlotSource {
    if (input < spec.left_slot_count) {
        if (spec.left_form_profile != 0) return vectorSlotSourceFromFormProfile(spec.left, spec.left_form_profile, input);
        return .{ .block = spec.left, .slot = input };
    }
    const right_slot = input - spec.left_slot_count;
    if (right_slot < spec.right_slot_count) {
        if (spec.right_form_profile != 0) return vectorSlotSourceFromFormProfile(spec.right, spec.right_form_profile, right_slot);
        return .{ .block = spec.right, .slot = right_slot };
    }
    return error.ProjectorWordTooLarge;
}

fn vectorSlotTarget(spec: VectorSlotProjectorSpec, output: u8) !VectorSlotSource {
    if (output >= spec.shape.box_count) return error.ProjectorWordTooLarge;
    if (spec.output_form_profile != 0) return vectorSlotSourceFromFormProfile(spec.output, spec.output_form_profile, output);
    return .{ .block = spec.output, .slot = output };
}

fn vectorSlotSourceFromFormProfile(index: rendering.IndexRef, profile: u128, slot: u8) !VectorSlotSource {
    var remaining: u16 = slot;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const count = profileSlot(profile, rank_index);
        if (count == 0) continue;
        const rank = rank_index + 1;
        const block_slot_count: u16 = @as(u16, count) * rank;
        if (remaining < block_slot_count) return .{
            .block = tensorFormRankBlock(index, rank),
            .slot = @intCast(remaining),
        };
        remaining -= block_slot_count;
    }
    return error.ProjectorWordTooLarge;
}

fn appendVectorYoungProjectionTerms(program: *VectorBrauerProgram, spec: VectorSlotProjectorSpec) !void {
    const rank = vectorYoungRank(spec) orelse return error.UnsupportedStructuralProjectorTerm;
    if (program.candidate_count == 0) return error.UnsupportedStructuralProjectorTerm;
    const shape = try normalizedVectorYoungShape(spec, rank);
    var projector = try traceFreeBrauerProjectorBasisForShape(shape, spec.dimension, program.candidates[0]);
    defer projector.deinit();
    try appendTraceFreeBrauerProjectorTerms(program, spec, projector);
}

fn appendTraceFreeBrauerProjectorTerms(program: *VectorBrauerProgram, spec: VectorSlotProjectorSpec, projector: TraceFreeBrauerProjector) !void {
    var basis_index: u8 = 0;
    while (basis_index < projector.basis_count) : (basis_index += 1) {
        const coefficient = projector.coefficients[basis_index];
        if (coefficient.numerator == 0) continue;
        try appendBrauerCandidateTermsScaled(program, spec, projector.basis[basis_index], coefficient);
    }
}

fn appendBrauerCandidateTerms(program: *VectorBrauerProgram, spec: VectorSlotProjectorSpec, candidate: BrauerCandidate) !void {
    try appendBrauerCandidateTermsScaled(program, spec, candidate, Rational.one());
}

fn countVectorYoungProjectionTerms(spec: VectorSlotProjectorSpec) !u16 {
    const rank = vectorYoungRank(spec) orelse return error.UnsupportedStructuralProjectorTerm;
    const program = try compileVectorYoungBrauerCore(spec);
    if (program.candidate_count == 0) return error.UnsupportedStructuralProjectorTerm;
    const shape = try normalizedVectorYoungShape(spec, rank);
    var projector = try traceFreeBrauerProjectorBasisForShape(shape, spec.dimension, program.candidates[0]);
    defer projector.deinit();
    var count: u16 = 0;
    var basis_index: u8 = 0;
    while (basis_index < projector.basis_count) : (basis_index += 1) {
        const scale = projector.coefficients[basis_index];
        if (scale.numerator == 0) continue;
        const candidate = projector.basis[basis_index];
        var word_index: u8 = 0;
        while (word_index < candidate.word_count) : (word_index += 1) {
            const coefficient = try candidate.words[word_index].coefficient.mul(scale);
            if (coefficient.numerator == 0) continue;
            if (count == std.math.maxInt(u16)) return error.UnsupportedTensorPrimitiveTermCap;
            count += 1;
        }
    }
    if (count == 0) return error.UnsupportedStructuralProjectorTerm;
    return count;
}

fn vectorYoungProjectionTermAt(spec: VectorSlotProjectorSpec, term_index: u16) !VectorBrauerTerm {
    const rank = vectorYoungRank(spec) orelse return error.UnsupportedStructuralProjectorTerm;
    const program = try compileVectorYoungBrauerCore(spec);
    if (program.candidate_count == 0) return error.UnsupportedStructuralProjectorTerm;
    const shape = try normalizedVectorYoungShape(spec, rank);
    var projector = try traceFreeBrauerProjectorBasisForShape(shape, spec.dimension, program.candidates[0]);
    defer projector.deinit();
    var seen: u16 = 0;
    var basis_index: u8 = 0;
    while (basis_index < projector.basis_count) : (basis_index += 1) {
        const scale = projector.coefficients[basis_index];
        if (scale.numerator == 0) continue;
        const candidate = projector.basis[basis_index];
        var word_index: u8 = 0;
        while (word_index < candidate.word_count) : (word_index += 1) {
            const coefficient = try candidate.words[word_index].coefficient.mul(scale);
            if (coefficient.numerator == 0) continue;
            if (seen == term_index) {
                var term = try vectorBrauerTerm(coefficient);
                try appendVectorBrauerWordTermAtoms(&term, spec, candidate.words[word_index], false);
                canonicalizeVectorBrauerTerm(&term);
                return term;
            }
            seen += 1;
        }
    }
    return error.ProjectorConstructorTermOutOfBounds;
}

fn appendBrauerCandidateTermsScaled(program: *VectorBrauerProgram, spec: VectorSlotProjectorSpec, candidate: BrauerCandidate, scale: Rational) !void {
    if (scale.numerator == 0) return;
    var word_index: u8 = 0;
    while (word_index < candidate.word_count) : (word_index += 1) {
        const coefficient = try candidate.words[word_index].coefficient.mul(scale);
        if (coefficient.numerator == 0) continue;
        var term = try vectorBrauerTerm(coefficient);
        try appendVectorBrauerWordTermAtoms(&term, spec, candidate.words[word_index], false);
        canonicalizeVectorBrauerTerm(&term);
        try appendMergedVectorBrauerTerm(program, term);
    }
}

fn brauerInnerProduct(dimension: u16, rank: u8, left: BrauerWord, right: BrauerWord) !Rational {
    var graph: BrauerContraction = .{};
    graph.init(rank);
    try graph.addInnerProductWord(rank, left, false);
    try graph.addInnerProductWord(rank, right, true);
    var slot: u8 = 0;
    while (slot < rank) : (slot += 1) {
        graph.unite(slot, @as(u8, 2 * rank + slot));
        graph.unite(@as(u8, rank + slot), @as(u8, 3 * rank + slot));
    }
    const loops = graph.countComponents(4 * rank);
    return try (try left.coefficient.mul(right.coefficient)).mul(try powRational(dimension, loops));
}

fn tensorContractionCandidateInnerProduct(spec: TensorContractionSpec, left: BrauerCandidate, right: BrauerCandidate) !Rational {
    const input_count = spec.left_slot_count + spec.right_slot_count;
    const output_count = spec.shape.box_count;
    var acc = Rational.zero();
    var left_index: u8 = 0;
    while (left_index < left.word_count) : (left_index += 1) {
        var right_index: u8 = 0;
        while (right_index < right.word_count) : (right_index += 1) {
            const value = try tensorContractionWordInnerProduct(spec.dimension, input_count, output_count, left.words[left_index], right.words[right_index]);
            acc = try acc.add(value);
        }
    }
    return acc;
}

fn tensorContractionWordInnerProduct(dimension: u16, input_count: u8, output_count: u8, left: BrauerWord, right: BrauerWord) !Rational {
    if (input_count + output_count > 2 * max_vector_young_boxes) return error.UnsupportedTensorShapeOverCap;
    var graph: BrauerContraction = .{};
    const left_input_base: u8 = 0;
    const left_output_base = input_count;
    const right_input_base = input_count + output_count;
    const right_output_base = right_input_base + input_count;
    const node_count = right_output_base + output_count;
    graph.initNodeCount(node_count);
    try graph.addRectangularWord(left_input_base, left_output_base, left);
    try graph.addRectangularWord(right_input_base, right_output_base, right);

    var slot: u8 = 0;
    while (slot < input_count) : (slot += 1) {
        graph.unite(left_input_base + slot, right_input_base + slot);
    }
    slot = 0;
    while (slot < output_count) : (slot += 1) {
        graph.unite(left_output_base + slot, right_output_base + slot);
    }

    const loops = graph.countComponents(node_count);
    return try (try left.coefficient.mul(right.coefficient)).mul(try powRational(dimension, loops));
}

fn selectVectorBrauerGramPivots(dimension: u8, entries: []const Rational) !VectorBrauerPivotSelection {
    if (dimension > max_vector_brauer_candidates) return error.GramMatrixTooLarge;
    const width: usize = dimension;
    if (entries.len < width * width) return error.InvalidGramMatrixSize;

    const prime: i64 = 1_000_000_007;
    var matrix: [max_vector_brauer_candidates * max_vector_brauer_candidates]i64 = [_]i64{0} ** (max_vector_brauer_candidates * max_vector_brauer_candidates);
    var row: usize = 0;
    while (row < width) : (row += 1) {
        var column: usize = 0;
        while (column < width) : (column += 1) {
            const value = entries[row * width + column];
            const numerator = positiveMod(value.numerator, prime);
            const denominator = positiveMod(value.denominator, prime);
            matrix[row * max_vector_brauer_candidates + column] = @mod(numerator * modularInverse(denominator, prime), prime);
        }
    }

    var selection: VectorBrauerPivotSelection = .{};
    var pivot_row: usize = 0;
    var pivot_column: usize = 0;
    while (pivot_column < width and pivot_row < width) : (pivot_column += 1) {
        const source_row = findModularPivotRow(matrix[0..], width, pivot_row, pivot_column) orelse continue;
        if (source_row != pivot_row) swapModularGramRows(matrix[0..], pivot_row, source_row);
        const pivot = matrix[pivot_row * max_vector_brauer_candidates + pivot_column];
        const pivot_inverse = modularInverse(pivot, prime);

        var column = pivot_column;
        while (column < width) : (column += 1) {
            matrix[pivot_row * max_vector_brauer_candidates + column] = @mod(matrix[pivot_row * max_vector_brauer_candidates + column] * pivot_inverse, prime);
        }

        row = 0;
        while (row < width) : (row += 1) {
            if (row == pivot_row) continue;
            const factor = matrix[row * max_vector_brauer_candidates + pivot_column];
            if (factor == 0) continue;
            column = pivot_column;
            while (column < width) : (column += 1) {
                const value = matrix[row * max_vector_brauer_candidates + column] - @mod(factor * matrix[pivot_row * max_vector_brauer_candidates + column], prime);
                matrix[row * max_vector_brauer_candidates + column] = positiveMod(value, prime);
            }
        }

        selection.pivots[selection.count] = @intCast(pivot_column);
        selection.count += 1;
        pivot_row += 1;
    }
    return selection;
}

fn findModularPivotRow(matrix: []const i64, width: usize, first_row: usize, column: usize) ?usize {
    var row = first_row;
    while (row < width) : (row += 1) {
        if (matrix[row * max_vector_brauer_candidates + column] != 0) return row;
    }
    return null;
}

fn swapModularGramRows(matrix: []i64, left: usize, right: usize) void {
    var column: usize = 0;
    while (column < max_vector_brauer_candidates) : (column += 1) {
        const left_index = left * max_vector_brauer_candidates + column;
        const right_index = right * max_vector_brauer_candidates + column;
        const temporary = matrix[left_index];
        matrix[left_index] = matrix[right_index];
        matrix[right_index] = temporary;
    }
}

fn positiveMod(value: i64, modulus: i64) i64 {
    const reduced = @mod(value, modulus);
    return if (reduced < 0) reduced + modulus else reduced;
}

fn modularInverse(value: i64, modulus: i64) i64 {
    var base = positiveMod(value, modulus);
    var exponent: i64 = modulus - 2;
    var result: i64 = 1;
    while (exponent != 0) : (exponent >>= 1) {
        if ((exponent & 1) != 0) result = @mod(result * base, modulus);
        base = @mod(base * base, modulus);
    }
    return result;
}

const BrauerContraction = struct {
    parent: [6 * max_tensor_slots]u8 = [_]u8{0} ** (6 * max_tensor_slots),

    fn init(self: *BrauerContraction, rank: u8) void {
        self.initNodeCount(4 * rank);
    }

    fn initNodeCount(self: *BrauerContraction, node_count: u8) void {
        var index: u8 = 0;
        while (index < node_count) : (index += 1) {
            self.parent[index] = index;
        }
    }

    fn find(self: *BrauerContraction, node: u8) u8 {
        var root = node;
        while (self.parent[root] != root) {
            root = self.parent[root];
        }
        var current = node;
        while (self.parent[current] != current) {
            const next = self.parent[current];
            self.parent[current] = root;
            current = next;
        }
        return root;
    }

    fn unite(self: *BrauerContraction, left: u8, right: u8) void {
        const left_root = self.find(left);
        const right_root = self.find(right);
        if (left_root != right_root) self.parent[right_root] = left_root;
    }

    fn addInnerProductWord(self: *BrauerContraction, rank: u8, word: BrauerWord, right_word: bool) !void {
        const input_base: u8 = if (right_word) 2 * rank else 0;
        const output_base: u8 = if (right_word) 3 * rank else rank;
        var edge_index: u8 = 0;
        while (edge_index < word.edge_count) : (edge_index += 1) {
            const edge = word.edges[edge_index];
            switch (edge.kind) {
                .delta => self.unite(input_base + edge.input_a, output_base + edge.output_a),
                .input_trace => self.unite(input_base + edge.input_a, input_base + edge.input_b),
                .output_metric => self.unite(output_base + edge.output_a, output_base + edge.output_b),
            }
        }
    }

    fn addRectangularWord(self: *BrauerContraction, input_base: u8, output_base: u8, word: BrauerWord) !void {
        var edge_index: u8 = 0;
        while (edge_index < word.edge_count) : (edge_index += 1) {
            const edge = word.edges[edge_index];
            switch (edge.kind) {
                .delta => self.unite(input_base + edge.input_a, output_base + edge.output_a),
                .input_trace => self.unite(input_base + edge.input_a, input_base + edge.input_b),
                .output_metric => self.unite(output_base + edge.output_a, output_base + edge.output_b),
            }
        }
    }

    fn addRemappedSquareWord(self: *BrauerContraction, input_base: u8, output_base: u8, word: BrauerWord, offset: u8) !void {
        var edge_index: u8 = 0;
        while (edge_index < word.edge_count) : (edge_index += 1) {
            const edge = word.edges[edge_index];
            switch (edge.kind) {
                .delta => self.unite(input_base + offset + edge.input_a, output_base + offset + edge.output_a),
                .input_trace => self.unite(input_base + offset + edge.input_a, input_base + offset + edge.input_b),
                .output_metric => self.unite(output_base + offset + edge.output_a, output_base + offset + edge.output_b),
            }
        }
    }

    fn addCompositionLeftWord(self: *BrauerContraction, rank: u8, word: BrauerWord) !void {
        const middle_base = rank;
        const output_base = 2 * rank;
        var edge_index: u8 = 0;
        while (edge_index < word.edge_count) : (edge_index += 1) {
            const edge = word.edges[edge_index];
            switch (edge.kind) {
                .delta => self.unite(middle_base + edge.input_a, output_base + edge.output_a),
                .input_trace => self.unite(middle_base + edge.input_a, middle_base + edge.input_b),
                .output_metric => self.unite(output_base + edge.output_a, output_base + edge.output_b),
            }
        }
    }

    fn addCompositionRightWord(self: *BrauerContraction, rank: u8, word: BrauerWord) !void {
        const source_base = 0;
        const middle_base = rank;
        var edge_index: u8 = 0;
        while (edge_index < word.edge_count) : (edge_index += 1) {
            const edge = word.edges[edge_index];
            switch (edge.kind) {
                .delta => self.unite(source_base + edge.input_a, middle_base + edge.output_a),
                .input_trace => self.unite(source_base + edge.input_a, source_base + edge.input_b),
                .output_metric => self.unite(middle_base + edge.output_a, middle_base + edge.output_b),
            }
        }
    }

    fn addCompositionRightAdjointWord(self: *BrauerContraction, rank: u8, word: BrauerWord) !void {
        const source_base = 0;
        const middle_base = rank;
        var edge_index: u8 = 0;
        while (edge_index < word.edge_count) : (edge_index += 1) {
            const edge = word.edges[edge_index];
            switch (edge.kind) {
                .delta => self.unite(source_base + edge.output_a, middle_base + edge.input_a),
                .input_trace => self.unite(middle_base + edge.input_a, middle_base + edge.input_b),
                .output_metric => self.unite(source_base + edge.output_a, source_base + edge.output_b),
            }
        }
    }

    fn countComponents(self: *BrauerContraction, node_count: u8) u8 {
        var count: u8 = 0;
        var node: u8 = 0;
        while (node < node_count) : (node += 1) {
            if (self.find(node) == node) count += 1;
        }
        return count;
    }
};

fn powRational(base: u16, exponent: u8) !Rational {
    var value: i64 = 1;
    var index: u8 = 0;
    while (index < exponent) : (index += 1) {
        value = try checkedMulI64(value, base);
    }
    return Rational.init(value, 1);
}

fn invertVectorBrauerGram(dimension: u8, entries: []const Rational) ![max_vector_brauer_gram_entries]Rational {
    if (dimension > max_vector_brauer_candidates) return error.GramMatrixTooLarge;
    const width: usize = dimension;
    if (entries.len < width * width) return error.InvalidGramMatrixSize;

    var matrix: [max_vector_brauer_candidates * max_vector_brauer_candidates * 2]WideRational = [_]WideRational{WideRational.zero()} ** (max_vector_brauer_candidates * max_vector_brauer_candidates * 2);
    var row: usize = 0;
    while (row < width) : (row += 1) {
        var column: usize = 0;
        while (column < width) : (column += 1) {
            matrix[row * max_vector_brauer_candidates * 2 + column] = WideRational.fromRational(entries[row * width + column]);
            matrix[row * max_vector_brauer_candidates * 2 + width + column] = if (row == column) WideRational.one() else WideRational.zero();
        }
    }

    var pivot_row: usize = 0;
    while (pivot_row < width) : (pivot_row += 1) {
        const source_row = findVectorBrauerAugmentedPivotRow(matrix[0..], width, pivot_row) orelse return error.SingularGramMatrix;
        if (source_row != pivot_row) swapVectorBrauerAugmentedRows(matrix[0..], width, pivot_row, source_row);

        const pivot = matrix[pivot_row * max_vector_brauer_candidates * 2 + pivot_row];
        var column: usize = 0;
        while (column < width * 2) : (column += 1) {
            matrix[pivot_row * max_vector_brauer_candidates * 2 + column] = try matrix[pivot_row * max_vector_brauer_candidates * 2 + column].div(pivot);
        }

        row = 0;
        while (row < width) : (row += 1) {
            if (row == pivot_row) continue;
            const factor = matrix[row * max_vector_brauer_candidates * 2 + pivot_row];
            if (factor.numerator == 0) continue;
            column = 0;
            while (column < width * 2) : (column += 1) {
                const scaled = try factor.mul(matrix[pivot_row * max_vector_brauer_candidates * 2 + column]);
                matrix[row * max_vector_brauer_candidates * 2 + column] = try matrix[row * max_vector_brauer_candidates * 2 + column].sub(scaled);
            }
        }
    }

    var inverse: [max_vector_brauer_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_vector_brauer_gram_entries;
    row = 0;
    while (row < width) : (row += 1) {
        var column: usize = 0;
        while (column < width) : (column += 1) {
            inverse[row * width + column] = try matrix[row * max_vector_brauer_candidates * 2 + width + column].toRational();
        }
    }
    return inverse;
}

fn findVectorBrauerAugmentedPivotRow(matrix: []const WideRational, width: usize, first_row: usize) ?usize {
    var row = first_row;
    while (row < width) : (row += 1) {
        if (matrix[row * max_vector_brauer_candidates * 2 + first_row].numerator != 0) return row;
    }
    return null;
}

fn swapVectorBrauerAugmentedRows(matrix: []WideRational, width: usize, left: usize, right: usize) void {
    var column: usize = 0;
    while (column < width * 2) : (column += 1) {
        const left_index = left * max_vector_brauer_candidates * 2 + column;
        const right_index = right * max_vector_brauer_candidates * 2 + column;
        const temporary = matrix[left_index];
        matrix[left_index] = matrix[right_index];
        matrix[right_index] = temporary;
    }
}

fn vectorBrauerTerm(coefficient: Rational) !VectorBrauerTerm {
    if (coefficient.numerator == 0) return error.ZeroVectorBrauerTerm;
    return .{ .coefficient = coefficient };
}

fn vectorBrauerTermDelta(term: *VectorBrauerTerm, upper: rendering.IndexBlockId, upper_slot: u8, lower: rendering.IndexBlockId, lower_slot: u8) !void {
    if (term.atom_count == max_vector_brauer_atoms) return error.UnsupportedTensorPrimitiveTermCap;
    term.atoms[term.atom_count] = .{ .kind = .delta, .upper = upper, .upper_slot = upper_slot, .lower = lower, .lower_slot = lower_slot };
    term.atom_count += 1;
}

fn vectorBrauerTermMetric(term: *VectorBrauerTerm, left: rendering.IndexBlockId, left_slot: u8, right: rendering.IndexBlockId, right_slot: u8) !void {
    if (term.atom_count == max_vector_brauer_atoms) return error.UnsupportedTensorPrimitiveTermCap;
    term.atoms[term.atom_count] = .{ .kind = .metric, .left = left, .left_slot = left_slot, .right = right, .right_slot = right_slot };
    term.atom_count += 1;
}

fn vectorBrauerTermHodgeStar(term: *VectorBrauerTerm, input: rendering.IndexBlockId, output: rendering.IndexBlockId) !void {
    if (term.atom_count == max_vector_brauer_atoms) return error.UnsupportedTensorPrimitiveTermCap;
    term.atoms[term.atom_count] = .{ .kind = .hodge_star, .hodge_input = input, .hodge_output = output };
    term.atom_count += 1;
}

fn appendVectorBrauerTerm(program: *VectorBrauerProgram, term: VectorBrauerTerm) !void {
    if (term.coefficient.numerator == 0) return;
    if (program.term_count == max_vector_brauer_terms) return error.UnsupportedTensorPrimitiveTermCap;
    program.terms[program.term_count] = term;
    program.term_count += 1;
}

fn compileStructuralProjectorProgram(spec: StructuralProjectorSpec) !ProjectorProgram {
    return compileProjectorProgramForChannel(.{ .structural_projection = spec }, orthogonalStructuralProjectionBackend());
}

fn structuralProjectorSpecFromTensorForm(spec: TensorFormProjectionSpec) StructuralProjectorSpec {
    return .{
        .operator_id = spec.operator_id,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .left = .{
            .index = spec.left,
            .form_profile = spec.input_form_profile,
            .form_mask = spec.input_form_mask,
            .form_count = @intCast(profileTotalPower(spec.input_form_profile)),
            .has_spinor = true,
            .chirality = spec.chirality,
        },
        .right = .{
            .index = spec.right,
            .has_spinor = true,
            .chirality = spec.right_chirality,
        },
        .output = .{
            .index = spec.output,
            .form_profile = spec.output_form_profile,
            .form_count = spec.output_form_count,
            .form_rank = spec.output_form_rank,
            .form_duality = spec.output_duality,
        },
    };
}

fn structuralProjectorSpecFromTensorSpinor(spec: TensorSpinorProjectionSpec) StructuralProjectorSpec {
    const input_tower_power = if (!spec.left_has_spinor) 0 else if (spec.input_tower_power == 0) spec.tower_power + 1 else spec.input_tower_power;
    return .{
        .operator_id = spec.operator_id,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .left = .{
            .index = spec.left,
            .form_profile = spec.input_form_profile,
            .form_mask = profileMask(spec.input_form_profile),
            .form_count = spec.input_form_count,
            .tower_power = input_tower_power,
            .has_spinor = spec.left_has_spinor,
            .chirality = spec.chirality,
        },
        .right = .{
            .index = spec.right,
            .has_spinor = spec.right_has_spinor,
            .chirality = if (spec.right_chirality == 255) spec.chirality else spec.right_chirality,
        },
        .output = .{
            .index = spec.output,
            .form_profile = spec.form_profile,
            .form_mask = spec.form_mask,
            .form_count = spec.form_count,
            .form_rank = spec.form_rank,
            .form_duality = spec.duality,
            .tower_power = spec.tower_power,
            .has_spinor = spec.output_has_spinor,
            .chirality = spec.chirality,
        },
    };
}

fn structuralProgramKey(spec: StructuralProjectorSpec) StructuralProgramKey {
    return .{
        .dimension = spec.orthogonal_dimension,
        .source_form_profile = spec.left.form_profile,
        .target_form_profile = spec.output.form_profile,
        .source_young_row_count = spec.left.young_row_count,
        .source_young_rows = spec.left.young_rows,
        .source_young_box_count = spec.left.young_box_count,
        .right_young_row_count = spec.right.young_row_count,
        .right_young_rows = spec.right.young_rows,
        .right_young_box_count = spec.right.young_box_count,
        .target_young_row_count = spec.output.young_row_count,
        .target_young_rows = spec.output.young_rows,
        .target_young_box_count = spec.output.young_box_count,
        .source_tower_power = spec.left.tower_power,
        .target_tower_power = spec.output.tower_power,
        .source_has_spinor = spec.left.has_spinor,
        .right_has_spinor = spec.right.has_spinor,
        .target_has_spinor = spec.output.has_spinor,
        .source_chirality = spec.left.chirality,
        .right_chirality = spec.right.chirality,
        .target_chirality = spec.output.chirality,
        .duality = spec.output.form_duality,
    };
}

fn structuralProjectorKeySummary(key: StructuralProgramKey) StructuralProjectorKeySummary {
    return .{
        .dimension = key.dimension,
        .source_form_profile = key.source_form_profile,
        .target_form_profile = key.target_form_profile,
        .source_tower_power = key.source_tower_power,
        .target_tower_power = key.target_tower_power,
        .source_has_spinor = key.source_has_spinor,
        .right_has_spinor = key.right_has_spinor,
        .target_has_spinor = key.target_has_spinor,
        .source_chirality = key.source_chirality,
        .right_chirality = key.right_chirality,
        .target_chirality = key.target_chirality,
        .duality = key.duality,
    };
}

fn structuralProgramKeyHash(key: StructuralProgramKey) u64 {
    var hash: u64 = 0xcbf29ce484222325;
    hashMixU64(&hash, key.dimension);
    hashMixU128(&hash, key.source_form_profile);
    hashMixU128(&hash, key.target_form_profile);
    structuralEndpointYoungKeyHash(&hash, key.source_young_row_count, key.source_young_rows, key.source_young_box_count);
    structuralEndpointYoungKeyHash(&hash, key.right_young_row_count, key.right_young_rows, key.right_young_box_count);
    structuralEndpointYoungKeyHash(&hash, key.target_young_row_count, key.target_young_rows, key.target_young_box_count);
    hashMixU64(&hash, key.source_tower_power);
    hashMixU64(&hash, key.target_tower_power);
    hashMixU64(&hash, @intFromBool(key.source_has_spinor));
    hashMixU64(&hash, @intFromBool(key.right_has_spinor));
    hashMixU64(&hash, @intFromBool(key.target_has_spinor));
    hashMixU64(&hash, key.source_chirality);
    hashMixU64(&hash, key.right_chirality);
    hashMixU64(&hash, key.target_chirality);
    hashMixU64(&hash, @intFromEnum(key.duality));
    hashMixU64(&hash, key.signature_sequence_hash);
    return if (hash == 0) 1 else hash;
}

fn structuralEndpointYoungKeyHash(hash: *u64, row_count: u8, rows: [max_young_rows]u8, box_count: u8) void {
    hashMixU64(hash, row_count);
    hashMixU64(hash, box_count);
    var row: u8 = 0;
    while (row < row_count) : (row += 1) {
        hashMixU64(hash, rows[row]);
    }
}

fn cachedVectorProgramKey(kind: CachedVectorProgramKind, spec: VectorSlotProjectorSpec) CachedVectorProgramKey {
    return .{
        .kind = kind,
        .dimension = spec.dimension,
        .left = spec.left,
        .left_slot_count = spec.left_slot_count,
        .left_form_profile = spec.left_form_profile,
        .right = spec.right,
        .right_slot_count = spec.right_slot_count,
        .right_form_profile = spec.right_form_profile,
        .output = spec.output,
        .output_form_profile = spec.output_form_profile,
        .row_count = spec.shape.row_count,
        .rows = spec.shape.rows,
        .box_count = spec.shape.box_count,
    };
}

fn cachedVectorProgramKeyHash(key: CachedVectorProgramKey) u64 {
    var hash: u64 = 0xcbf29ce484222325;
    hashMixU64(&hash, @intFromEnum(key.kind));
    hashMixU64(&hash, key.dimension);
    hashMixU64(&hash, key.left);
    hashMixU64(&hash, key.left_slot_count);
    hashMixU128(&hash, key.left_form_profile);
    hashMixU64(&hash, key.right);
    hashMixU64(&hash, key.right_slot_count);
    hashMixU128(&hash, key.right_form_profile);
    hashMixU64(&hash, key.output);
    hashMixU128(&hash, key.output_form_profile);
    hashMixU64(&hash, key.row_count);
    hashMixU64(&hash, key.box_count);
    var row: u8 = 0;
    while (row < key.row_count) : (row += 1) {
        hashMixU64(&hash, key.rows[row]);
    }
    return if (hash == 0) 1 else hash;
}

fn hashMixU128(hash: *u64, value: u128) void {
    hashMixU64(hash, @truncate(value));
    hashMixU64(hash, @truncate(value >> 64));
}

fn hashMixI64(hash: *u64, value: i64) void {
    hashMixU64(hash, @bitCast(value));
}

fn hashMixU64(hash: *u64, value: u64) void {
    var mixed = value;
    var byte_index: u8 = 0;
    while (byte_index < 8) : (byte_index += 1) {
        hash.* ^= mixed & 0xff;
        hash.* *%= 0x100000001b3;
        mixed >>= 8;
    }
}

fn cachedVectorProgramKeyEql(left: CachedVectorProgramKey, right: CachedVectorProgramKey) bool {
    if (left.kind != right.kind or
        left.dimension != right.dimension or
        left.left != right.left or
        left.left_slot_count != right.left_slot_count or
        left.left_form_profile != right.left_form_profile or
        left.right != right.right or
        left.right_slot_count != right.right_slot_count or
        left.right_form_profile != right.right_form_profile or
        left.output != right.output or
        left.output_form_profile != right.output_form_profile or
        left.row_count != right.row_count or
        left.box_count != right.box_count) return false;
    var row: u8 = 0;
    while (row < left.row_count) : (row += 1) {
        if (left.rows[row] != right.rows[row]) return false;
    }
    return true;
}

fn structuralProgramKeyEql(left: StructuralProgramKey, right: StructuralProgramKey) bool {
    return left.dimension == right.dimension and
        left.source_form_profile == right.source_form_profile and
        left.target_form_profile == right.target_form_profile and
        structuralEndpointYoungKeyEql(left.source_young_row_count, left.source_young_rows, left.source_young_box_count, right.source_young_row_count, right.source_young_rows, right.source_young_box_count) and
        structuralEndpointYoungKeyEql(left.right_young_row_count, left.right_young_rows, left.right_young_box_count, right.right_young_row_count, right.right_young_rows, right.right_young_box_count) and
        structuralEndpointYoungKeyEql(left.target_young_row_count, left.target_young_rows, left.target_young_box_count, right.target_young_row_count, right.target_young_rows, right.target_young_box_count) and
        left.source_tower_power == right.source_tower_power and
        left.target_tower_power == right.target_tower_power and
        left.source_has_spinor == right.source_has_spinor and
        left.right_has_spinor == right.right_has_spinor and
        left.target_has_spinor == right.target_has_spinor and
        left.source_chirality == right.source_chirality and
        left.right_chirality == right.right_chirality and
        left.target_chirality == right.target_chirality and
        left.duality == right.duality and
        left.signature_sequence_hash == right.signature_sequence_hash;
}

fn structuralEndpointYoungKeyEql(left_row_count: u8, left_rows: [max_young_rows]u8, left_box_count: u8, right_row_count: u8, right_rows: [max_young_rows]u8, right_box_count: u8) bool {
    if (left_row_count != right_row_count or left_box_count != right_box_count) return false;
    var row: u8 = 0;
    while (row < left_row_count) : (row += 1) {
        if (left_rows[row] != right_rows[row]) return false;
    }
    return true;
}

fn compileProjectorProgramForChannel(channel: ProjectorChannel, backend: ProjectorBackend) !ProjectorProgram {
    var candidates: ProjectorCandidateBuffer = .{};
    try backend.enumerate_candidates(backend.context, channel, &candidates);
    if (candidates.count == 0) return switch (channel) {
        .structural_projection => error.UnsupportedStructuralProjectorTerm,
        .tensor_form_projection => error.UnsupportedTensorFormProjectionTerm,
        .tensor_spinor_projection => error.UnsupportedTensorSpinorProjectionTerm,
        .vector_spinor_traceless => error.UnsupportedProjectorProgram,
    };
    const gram_context: ProjectorChannelGramContext = .{
        .channel = channel,
        .backend = backend,
    };
    return compileProjectorProgram(candidates, .{
        .context = &gram_context,
        .inner_product = projectorChannelInnerProduct,
    });
}

fn projectorChannelInnerProduct(context: ?*const anyopaque, left: ProjectorCandidateWord, right: ProjectorCandidateWord) !Rational {
    const gram_context: *const ProjectorChannelGramContext = @ptrCast(@alignCast(context orelse return error.InvalidProjectorBackend));
    return gram_context.backend.inner_product(gram_context.backend.context, gram_context.channel, left, right);
}

fn compileProjectorProgram(candidates: ProjectorCandidateBuffer, gram_rules: ProjectorCandidateGram) !ProjectorProgram {
    if (candidates.count == 0) return error.UnsupportedProjectorProgram;
    var gram: [max_program_candidate_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_program_candidate_gram_entries;
    var row: usize = 0;
    while (row < candidates.count) : (row += 1) {
        var column: usize = 0;
        while (column <= row) : (column += 1) {
            const value = try gram_rules.inner_product(gram_rules.context, candidates.words[row], candidates.words[column]);
            gram[row * candidates.count + column] = value;
            gram[column * candidates.count + row] = value;
        }
    }

    const pivots = try selectIndependentGramPivots(candidates.count, gram[0..]);
    if (pivots.count == 0) return error.SingularGramMatrix;

    var pivot_gram: [max_program_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_program_gram_entries;
    row = 0;
    while (row < pivots.count) : (row += 1) {
        var column: usize = 0;
        while (column < pivots.count) : (column += 1) {
            const source_row = pivots.pivots[row];
            const source_column = pivots.pivots[column];
            pivot_gram[row * pivots.count + column] = gram[@as(usize, source_row) * candidates.count + source_column];
        }
    }

    var program: ProjectorProgram = .{};
    program.candidate_count = candidates.count;
    program.pivot_count = pivots.count;
    program.candidates = candidates.words;
    var pivot_index: u8 = 0;
    while (pivot_index < pivots.count) : (pivot_index += 1) {
        program.pivots[pivot_index] = pivots.pivots[pivot_index];
    }
    program.inverse_gram = try invertSmallGram(pivots.count, pivot_gram[0..]);
    return program;
}

fn orthogonalStructuralProjectionBackend() ProjectorBackend {
    return .{
        .enumerate_candidates = orthogonalStructuralProjectionEnumerateCandidates,
        .inner_product = orthogonalStructuralProjectionInnerProduct,
    };
}

fn orthogonalStructuralProjectionEnumerateCandidates(_: ?*const anyopaque, channel: ProjectorChannel, candidates: *ProjectorCandidateBuffer) !void {
    const spec = switch (channel) {
        .structural_projection => |spec| spec,
        else => return error.UnsupportedStructuralProjectorTerm,
    };
    candidates.* = try enumerateOrthogonalStructuralCandidateWords(spec);
}

fn orthogonalStructuralProjectionInnerProduct(_: ?*const anyopaque, channel: ProjectorChannel, left: ProjectorCandidateWord, right: ProjectorCandidateWord) !Rational {
    switch (channel) {
        .structural_projection => {},
        else => return error.UnsupportedStructuralProjectorTerm,
    }
    return structuralCandidateInnerProduct(left, right);
}

fn enumerateOrthogonalStructuralCandidateWords(spec: StructuralProjectorSpec) !ProjectorCandidateBuffer {
    var buffer: ProjectorCandidateBuffer = .{};
    try enumerateStructuralEffectSearchCandidates(spec, &buffer);
    return buffer;
}

fn enumerateStructuralEffectSearchCandidates(spec: StructuralProjectorSpec, buffer: *ProjectorCandidateBuffer) !void {
    const start: StructuralSearchState = .{
        .form_profile = spec.left.form_profile,
        .tower_power = spec.left.tower_power,
        .chirality = spec.left.chirality,
        .has_spinor = spec.left.has_spinor,
    };
    const target: StructuralSearchState = .{
        .form_profile = spec.output.form_profile,
        .tower_power = spec.output.tower_power,
        .chirality = spec.output.chirality,
        .has_spinor = spec.output.has_spinor,
    };
    if (try appendFormOnlyUniformShiftDownTowerRaiseCandidate(spec, start, target, buffer)) return;
    if (try appendUniformShiftDownTowerRaiseCandidate(spec, start, target, buffer)) return;
    var word: ProjectorCandidateWord = .{};
    try searchStructuralEffectWords(spec, start, start, target, 0, &word, buffer);
}

fn generateOrthogonalStructuralPrimitiveEffects(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState) !StructuralPrimitiveEffectBuffer {
    var effects: StructuralPrimitiveEffectBuffer = .{};
    if (spec.output.form_duality != .none) {
        if (hodgeProjectSignature(spec, start, target)) |signature| {
            try effects.append(.{ .kind = .hodge_project, .next = target, .signature = signature });
        }
        return effects;
    }

    if (start.has_spinor and spec.right.has_spinor and target.has_spinor) {
        const start_chirality = structuralStateChirality(start, spec.left.chirality);
        const target_chirality = structuralStateChirality(target, spec.output.chirality);
        const same_chirality = start_chirality == target_chirality and spec.right.chirality == start_chirality;
        const transform = classifyProfileTransform(start.form_profile, target.form_profile);
        if (same_chirality and start.tower_power == target.tower_power + 1 and (transform.kind == .shift_all_up or transform.kind == .move_rank_up)) {
            const next: StructuralSearchState = .{
                .form_profile = target.form_profile,
                .tower_power = target.tower_power,
                .chirality = target_chirality,
                .has_spinor = true,
            };
            if (gammaWedgeShiftSignature(spec, start, next)) |signature| {
                try effects.append(.{ .kind = .gamma_wedge_shift, .next = next, .signature = signature });
            }
        }
        if (start.tower_power == target.tower_power + 1 and start.form_profile != target.form_profile) {
            try appendGammaProfileMoveEffects(spec, start, target, &effects);
            if (spinorTargetGammaRankSplitSignature(spec, start, target)) |signature| {
                try appendUniqueStructuralEffect(&effects, .{ .kind = .gamma_rank_split, .next = target, .signature = signature });
            }
        }
        if (start.tower_power == target.tower_power and start.form_profile != target.form_profile) {
            try appendGammaProfileMoveEffects(spec, start, target, &effects);
            if (gammaProfileAddRankSignature(spec, start, target)) |signature| {
                try appendUniqueStructuralEffect(&effects, .{ .kind = .gamma_wedge_shift, .next = target, .signature = signature });
            }
        }
        if (start_chirality == target_chirality and start.tower_power > target.tower_power) {
            const tower_gap = start.tower_power - target.tower_power;
            const profile_deficit = profilePositiveDeficitPower(start.form_profile, target.form_profile);
            if (tower_gap > profile_deficit) {
                try effects.append(.{ .kind = .spinor_tower_contract, .next = .{
                    .form_profile = start.form_profile,
                    .tower_power = start.tower_power - 1,
                    .chirality = start_chirality,
                    .has_spinor = true,
                } });
            }
            if (!(same_chirality and start.tower_power == target.tower_power + 1 and (transform.kind == .shift_all_up or transform.kind == .move_rank_up))) {
                var rank_index: u8 = 0;
                while (rank_index < 32) : (rank_index += 1) {
                    if (profileSlot(start.form_profile, rank_index) >= profileSlot(target.form_profile, rank_index)) continue;
                    if (profileSlot(start.form_profile, rank_index) == 0xf) continue;
                    const rank = rank_index + 1;
                    try effects.append(.{ .kind = .spinor_tower_contract, .next = .{
                        .form_profile = profileIncrementedRank(start.form_profile, rank),
                        .tower_power = start.tower_power - 1,
                        .chirality = start_chirality,
                        .has_spinor = true,
                    } });
                }
            }
        }
        if (start_chirality != target_chirality and start.tower_power > target.tower_power + 1) {
            const next: StructuralSearchState = .{
                .form_profile = start.form_profile,
                .tower_power = start.tower_power - 1,
                .chirality = start_chirality,
                .has_spinor = true,
            };
            if (gammaProfileActionSignature(spec, next, target)) |signature| {
                if (signature.action.contraction_count != 0) {
                    try effects.append(.{ .kind = .spinor_tower_contract, .next = next });
                }
            }
        }
        if (same_chirality and start.tower_power < target.tower_power and start.form_profile == target.form_profile) {
            try effects.append(.{ .kind = .spinor_tower_contract_adjoint, .next = .{
                .form_profile = start.form_profile,
                .tower_power = start.tower_power + 1,
                .chirality = start_chirality,
                .has_spinor = true,
            } });
        }
        if (same_chirality and target.tower_power != std.math.maxInt(u16) and start.tower_power < target.tower_power + 1 and start.form_profile != target.form_profile) {
            const shift_transform = classifyProfileTransform(start.form_profile, target.form_profile);
            if (shift_transform.kind == .shift_all_up or shift_transform.kind == .move_rank_up) {
                try effects.append(.{ .kind = .spinor_tower_contract_adjoint, .next = .{
                    .form_profile = start.form_profile,
                    .tower_power = start.tower_power + 1,
                    .chirality = start_chirality,
                    .has_spinor = true,
                } });
            }
        }
        if (target.tower_power != std.math.maxInt(u16) and start.tower_power < target.tower_power + 1 and start.form_profile != target.form_profile) {
            const next: StructuralSearchState = .{
                .form_profile = start.form_profile,
                .tower_power = start.tower_power + 1,
                .chirality = start_chirality,
                .has_spinor = true,
            };
            if (profileTotalPower(next.form_profile) == profileTotalPower(target.form_profile)) {
                try effects.append(.{ .kind = .spinor_tower_contract_adjoint, .next = next });
            }
        }
        if (start_chirality == target_chirality and start.tower_power < target.tower_power) {
            var rank_index: u8 = 0;
            while (rank_index < 32) : (rank_index += 1) {
                if (profileSlot(start.form_profile, rank_index) <= profileSlot(target.form_profile, rank_index)) continue;
                const rank = rank_index + 1;
                var chirality_candidate: u8 = 1;
                while (chirality_candidate <= 2) : (chirality_candidate += 1) {
                    if (!spinorActionChiralityValid(spec.right.chirality, chirality_candidate, rank)) continue;
                    try effects.append(.{ .kind = .spinor_tower_contract_adjoint, .next = .{
                        .form_profile = profileDecrementedRank(start.form_profile, rank),
                        .tower_power = start.tower_power + 1,
                        .chirality = chirality_candidate,
                        .has_spinor = true,
                    } });
                }
            }
        }
        if (start_chirality == target_chirality and start.tower_power != std.math.maxInt(u16) and target.tower_power != std.math.maxInt(u16) and start.tower_power <= target.tower_power + 1 and profileTotalPower(start.form_profile) == profileTotalPower(target.form_profile) + 1 and classifyProfileTransform(start.form_profile, target.form_profile).kind == .unsupported) {
            var rank_index: u8 = 0;
            while (rank_index < 32) : (rank_index += 1) {
                if (profileSlot(start.form_profile, rank_index) == 0) continue;
                const rank = rank_index + 1;
                const removed_profile = profileDecrementedRank(start.form_profile, rank);
                const shift_transform = classifyProfileTransform(removed_profile, target.form_profile);
                const shifted_up = shift_transform.kind == .shift_all_up or shift_transform.kind == .move_rank_up;
                const moved_down = blk: {
                    const move = profileMovedAnyRank(removed_profile, target.form_profile) orelse break :blk false;
                    break :blk move.target_rank < move.source_rank;
                };
                if (!shifted_up and !moved_down) continue;
                const intermediate_chirality: u8 = if (moved_down and rank % 2 == 1 and target_chirality != 0) 3 - target_chirality else target_chirality;
                if (!spinorActionChiralityValid(spec.right.chirality, intermediate_chirality, rank)) continue;
                try effects.append(.{ .kind = .spinor_tower_contract_adjoint, .next = .{
                    .form_profile = removed_profile,
                    .tower_power = start.tower_power + 1,
                    .chirality = intermediate_chirality,
                    .has_spinor = true,
                } });
            }
        }
        return effects;
    }

    if (!start.has_spinor and spec.right.has_spinor and target.has_spinor) {
        if (spec.left.form_duality != .none and start.form_profile == 0 and spec.left.form_count == 1 and target.tower_power == 1) {
            const target_rank = profileOnlyRank(target.form_profile) orelse if (target.form_profile == 0) @as(u8, 0) else std.math.maxInt(u8);
            if (target_rank != std.math.maxInt(u8)) {
                const action = firstExteriorGammaAction(spec.orthogonal_dimension, spec.left.form_rank, target_rank, spec.left.form_duality) orelse return effects;
                if (spinorActionChiralityValid(spec.right.chirality, target.chirality, action.gamma_rank)) {
                    try effects.append(.{ .kind = .gamma_wedge_shift, .next = target, .signature = .{
                        .kind = .gamma_wedge_shift,
                        .input_block = tensorFormRankBlock(spec.left.index, spec.left.form_rank),
                        .output_block = if (target_rank == 0) 0 else tensorFormRankBlock(spec.output.index, target_rank),
                        .action = action,
                    } });
                    return effects;
                }
            }
        }
        if (start.tower_power == 0 and target.tower_power >= 1) {
            const target_chirality = structuralStateChirality(target, spec.output.chirality);
            if (target.tower_power == 1 and spec.right.chirality == target_chirality and (start.form_profile == target.form_profile or profileTotalPower(start.form_profile) == profileTotalPower(target.form_profile))) {
                try effects.append(.{ .kind = .form_spinor_contract_adjoint, .next = .{
                    .form_profile = start.form_profile,
                    .tower_power = 1,
                    .chirality = target_chirality,
                    .has_spinor = true,
                } });
            }
            const shifted_next: StructuralSearchState = .{
                .form_profile = start.form_profile,
                .tower_power = 1,
                .chirality = spec.right.chirality,
                .has_spinor = true,
            };
            const shifted_tower_source: StructuralSearchState = .{
                .form_profile = start.form_profile,
                .tower_power = if (target.tower_power == std.math.maxInt(u16)) target.tower_power else target.tower_power + 1,
                .chirality = spec.right.chirality,
                .has_spinor = true,
            };
            if (target.tower_power >= 1 and start.form_profile != target.form_profile and (gammaProfileActionSignature(spec, shifted_next, target) != null or gammaWedgeShiftSignature(spec, shifted_tower_source, target) != null)) {
                try effects.append(.{ .kind = .form_spinor_contract_adjoint, .next = .{
                    .form_profile = start.form_profile,
                    .tower_power = 1,
                    .chirality = spec.right.chirality,
                    .has_spinor = true,
                } });
            }
            var rank_index: u8 = 0;
            while (rank_index < 32) : (rank_index += 1) {
                if (profileSlot(start.form_profile, rank_index) <= profileSlot(target.form_profile, rank_index)) continue;
                const rank = rank_index + 1;
                var chirality_candidate: u8 = 1;
                while (chirality_candidate <= 2) : (chirality_candidate += 1) {
                    if (!spinorActionChiralityValid(spec.right.chirality, chirality_candidate, rank)) continue;
                    const removed_profile = profileDecrementedRank(start.form_profile, rank);
                    if (removed_profile == target.form_profile and target.tower_power == 1 and chirality_candidate != target_chirality) continue;
                    try effects.append(.{ .kind = .form_spinor_contract_adjoint, .next = .{
                        .form_profile = removed_profile,
                        .tower_power = 1,
                        .chirality = chirality_candidate,
                        .has_spinor = true,
                    } });
                }
            }
        }
        return effects;
    }

    const transform = classifyProfileTransform(start.form_profile, target.form_profile);
    if (start.has_spinor and spec.right.has_spinor and !target.has_spinor) {
        try enumerateTerminalExteriorGammaEffects(spec, start, target, &effects);
        if (effects.count != 0) return effects;
        if (start.tower_power == 0 and target.tower_power == 0 and transform.kind == .preserve) {
            const action = makeExteriorGammaAction(spec.orthogonal_dimension, 0, 0, 0, .none) orelse return effects;
            if (spinorBilinearChiralityValid(start.chirality, spec.right.chirality, terminalProfileBilinearParityRank(start.form_profile, target.form_profile))) {
                try effects.append(.{ .kind = .gamma_insert, .next = target, .signature = .{
                    .kind = .gamma_insert,
                    .input_block = spec.left.index,
                    .output_block = 0,
                    .action = action,
                } });
            }
        }
        if (start.tower_power == 0 and target.tower_power == 0 and transform.kind != .split_rank and inferTerminalGammaRank(start.form_profile, target.form_profile) != null) {
            if (gammaInsertSignature(spec, start, target)) |signature| {
                try effects.append(.{ .kind = .gamma_insert, .next = target, .signature = signature });
            }
        }
        if (start.tower_power == 0 and target.tower_power == 0 and transform.kind == .split_rank) {
            if (gammaRankSplitSignature(spec, start, target)) |signature| {
                try effects.append(.{ .kind = .gamma_rank_split, .next = target, .signature = signature });
            }
        }
        return effects;
    }
    return effects;
}

fn searchStructuralEffectWords(spec: StructuralProjectorSpec, origin: StructuralSearchState, current: StructuralSearchState, target: StructuralSearchState, depth: u8, word: *ProjectorCandidateWord, buffer: *ProjectorCandidateBuffer) !void {
    if (structuralSearchStateEql(current, target)) {
        if (depth != 0) try appendAcceptedStructuralWord(spec, origin, target, word.*, buffer);
        return;
    }
    if (depth == max_structural_search_depth) return;

    const effects = try generateOrthogonalStructuralPrimitiveEffects(spec, current, target);
    var effect_index: u8 = 0;
    while (effect_index < effects.count) : (effect_index += 1) {
        const effect = effects.slots[effect_index];
        if (structuralSearchStateEql(current, effect.next)) continue;
        var next_word = word.*;
        if (try appendStructuralEffectCandidate(spec, current, effect, &next_word)) {
            try searchStructuralEffectWords(spec, origin, effect.next, target, depth + 1, &next_word, buffer);
        }
    }
}

fn appendAcceptedStructuralWord(spec: StructuralProjectorSpec, origin: StructuralSearchState, target: StructuralSearchState, word: ProjectorCandidateWord, buffer: *ProjectorCandidateBuffer) !void {
    var accepted = word;
    const carried_profile = profileIntersection(origin.form_profile, target.form_profile);
    if (word.count != 0 and word.slots[0].kind == .gamma_insert) {
        appendCarriedFormDelta(&accepted, spec.left.index, spec.output.index, carried_profile, spec.orthogonal_dimension) catch |err| switch (err) {
            error.ProjectorWordTooLarge => return,
        };
    } else if (word.count != 0 and word.slots[0].kind == .gamma_wedge_shift) {
        return try appendUniqueStructuralCandidate(buffer, accepted);
    } else {
        appendFormProfileDeltas(&accepted, spec.left.index, spec.output.index, carried_profile, spec.orthogonal_dimension) catch |err| switch (err) {
            error.ProjectorWordTooLarge => return,
        };
    }
    try appendUniqueStructuralCandidate(buffer, accepted);
}

fn appendUniqueStructuralCandidate(buffer: *ProjectorCandidateBuffer, word: ProjectorCandidateWord) !void {
    var candidate_index: u8 = 0;
    while (candidate_index < buffer.count) : (candidate_index += 1) {
        if (projectorCandidateWordEql(buffer.words[candidate_index], word)) return;
    }
    try buffer.append(word);
}

fn appendUniformShiftDownTowerRaiseCandidate(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, buffer: *ProjectorCandidateBuffer) !bool {
    if (spec.output.form_duality != .none) return false;
    if (!start.has_spinor or !spec.right.has_spinor or !target.has_spinor) return false;
    if (target.tower_power != start.tower_power + 1) return false;
    if (start.tower_power > std.math.maxInt(u8) or target.tower_power > std.math.maxInt(u8)) return error.ProjectorProgramTooLarge;
    if (profileTotalPower(start.form_profile) == 0 or profileTotalPower(start.form_profile) != profileTotalPower(target.form_profile)) return false;
    const shift = profileUniformShiftDown(start.form_profile, target.form_profile) orelse return false;

    const removed_rank = highestShiftedSourceRank(start.form_profile, target.form_profile, shift) orelse return false;
    const lowered_rank = removed_rank - shift;
    const removed_profile = profileDecrementedRank(start.form_profile, removed_rank);
    var current: StructuralSearchState = .{
        .form_profile = removed_profile,
        .tower_power = target.tower_power,
        .chirality = spinorActionOutputChirality(spec.right.chirality, removed_rank),
        .has_spinor = true,
    };
    var word: ProjectorCandidateWord = .{};
    if (!try appendSpinorTowerContractAdjointEffect(spec, start, current, &word)) return false;

    var next: StructuralSearchState = .{
        .form_profile = profileIncrementedRank(current.form_profile, lowered_rank),
        .tower_power = target.tower_power,
        .chirality = spinorActionOutputChirality(current.chirality, lowered_rank),
        .has_spinor = true,
    };
    const add_signature = gammaProfileAddRankSignature(spec, current, next) orelse return false;
    if (!try appendGammaWedgeShiftSignatureEffect(spec, current, next, add_signature, &word)) return false;
    current = next;

    var step_count: u8 = 0;
    while (current.form_profile != target.form_profile) : (step_count += 1) {
        if (step_count == 32) return false;
        const move = nextUniformShiftDownMove(current.form_profile, target.form_profile, shift) orelse return false;
        const action = firstExteriorGammaAction(spec.orthogonal_dimension, move.source_rank, move.target_rank, .none) orelse return false;
        next = .{
            .form_profile = profileIncrementedRank(profileDecrementedRank(current.form_profile, move.source_rank), move.target_rank),
            .tower_power = target.tower_power,
            .chirality = spinorActionOutputChirality(current.chirality, action.gamma_rank),
            .has_spinor = true,
        };
        const move_signature = gammaProfileActionSignature(spec, current, next) orelse return false;
        if (!try appendGammaWedgeShiftSignatureEffect(spec, current, next, move_signature, &word)) return false;
        current = next;
    }
    if (!structuralSearchStateEql(current, target)) return false;
    try appendUniqueStructuralCandidate(buffer, word);
    return true;
}

fn appendFormOnlyUniformShiftDownTowerRaiseCandidate(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, buffer: *ProjectorCandidateBuffer) !bool {
    if (spec.output.form_duality != .none) return false;
    if (start.has_spinor or !spec.right.has_spinor or !target.has_spinor) return false;
    if (start.tower_power != 0 or target.tower_power != 1) return false;
    if (profileTotalPower(start.form_profile) == 0 or profileTotalPower(start.form_profile) != profileTotalPower(target.form_profile)) return false;
    const shift = profileUniformShiftDown(start.form_profile, target.form_profile) orelse return false;
    if (spec.right.chirality != target.chirality and profileTotalPower(start.form_profile) % 2 == 0) return false;

    var current: StructuralSearchState = .{
        .form_profile = start.form_profile,
        .tower_power = 1,
        .chirality = spec.right.chirality,
        .has_spinor = true,
    };
    var word: ProjectorCandidateWord = .{};
    if (!try appendFormSpinorContractAdjointEffect(spec, start, current, &word)) return false;

    var step_count: u8 = 0;
    while (current.form_profile != target.form_profile) : (step_count += 1) {
        if (step_count == 32) return false;
        const move = nextUniformShiftDownMove(current.form_profile, target.form_profile, shift) orelse return false;
        const action = firstExteriorGammaAction(spec.orthogonal_dimension, move.source_rank, move.target_rank, .none) orelse return false;
        const next: StructuralSearchState = .{
            .form_profile = profileIncrementedRank(profileDecrementedRank(current.form_profile, move.source_rank), move.target_rank),
            .tower_power = target.tower_power,
            .chirality = spinorActionOutputChirality(current.chirality, action.gamma_rank),
            .has_spinor = true,
        };
        const move_signature = gammaProfileActionSignature(spec, current, next) orelse return false;
        if (!try appendGammaWedgeShiftSignatureEffect(spec, current, next, move_signature, &word)) return false;
        current = next;
    }
    if (!structuralSearchStateEql(current, target)) return false;
    try appendUniqueStructuralCandidate(buffer, word);
    return true;
}

fn structuralSearchStateEql(left: StructuralSearchState, right: StructuralSearchState) bool {
    return left.form_profile == right.form_profile and
        left.tower_power == right.tower_power and
        left.chirality == right.chirality and
        left.has_spinor == right.has_spinor;
}

fn projectorCandidateWordEql(left: ProjectorCandidateWord, right: ProjectorCandidateWord) bool {
    if (left.count != right.count) return false;
    var slot_index: u8 = 0;
    while (slot_index < left.count) : (slot_index += 1) {
        if (!projectorPrimitiveEql(left.slots[slot_index], right.slots[slot_index])) return false;
    }
    return true;
}

fn structuralStateChirality(state: StructuralSearchState, fallback: u8) u8 {
    return if (state.chirality == 0 and state.has_spinor) fallback else state.chirality;
}

fn appendStructuralEffectCandidate(spec: StructuralProjectorSpec, start: StructuralSearchState, effect: StructuralPrimitiveEffect, word: *ProjectorCandidateWord) !bool {
    const target = effect.next;
    return switch (effect.kind) {
        .spinor_tower_contract => try appendSpinorTowerContractEffect(spec, start, target, word),
        .spinor_tower_contract_adjoint => try appendSpinorTowerContractAdjointEffect(spec, start, target, word),
        .form_spinor_contract_adjoint => try appendFormSpinorContractAdjointEffect(spec, start, target, word),
        .gamma_insert => if (effect.signature.kind == .gamma_insert) try appendGammaInsertSignatureEffect(spec, start, effect.signature, word) else try appendGammaInsertEffect(spec, start, target, word),
        .gamma_wedge_shift => if (effect.signature.kind == .gamma_wedge_shift) try appendGammaWedgeShiftSignatureEffect(spec, start, target, effect.signature, word) else try appendGammaWedgeShiftEffect(spec, start, target, word),
        .gamma_rank_split => if (effect.signature.kind == .gamma_rank_split) try appendGammaRankSplitSignatureEffect(spec, start, effect.signature, word) else try appendGammaRankSplitEffect(spec, start, target, word),
        .hodge_project => try appendHodgeProjectEffect(spec, start, target, word),
    };
}

fn enumerateTerminalExteriorGammaEffects(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, effects: *StructuralPrimitiveEffectBuffer) !void {
    if (!start.has_spinor or !spec.right.has_spinor or target.has_spinor) return;
    if (spec.output.form_duality != .none) return;
    if (start.tower_power != 0 or target.tower_power != 0) return;
    if (spec.orthogonal_dimension > std.math.maxInt(u8)) return;

    const dimension: u8 = @intCast(spec.orthogonal_dimension);
    try enumerateTerminalGammaInsertEffects(spec, start, target, dimension, effects);
    try enumerateTerminalGammaRankSplitEffects(spec, start, target, dimension, effects);
}

fn enumerateTerminalGammaInsertEffects(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, dimension: u8, effects: *StructuralPrimitiveEffectBuffer) !void {
    var gamma_rank: u8 = 1;
    while (gamma_rank <= dimension) : (gamma_rank += 1) {
        const action = makeExteriorGammaAction(spec.orthogonal_dimension, 0, gamma_rank, 0, .none) orelse continue;
        if (action.output_rank == 0) continue;
        if (!spinorBilinearChiralityValid(start.chirality, spec.right.chirality, terminalProfileBilinearParityRank(start.form_profile, target.form_profile))) continue;
        if (profileIncrementedRank(start.form_profile, action.output_rank) != target.form_profile) continue;
        const signature: PrimitiveSignature = .{
            .kind = .gamma_insert,
            .input_block = spec.left.index,
            .output_block = tensorFormInsertedBlock(spec.output.index, action.output_rank),
            .action = action,
            .tower_output_power = action.output_rank,
        };
        try appendUniqueStructuralEffect(effects, .{ .kind = .gamma_insert, .next = target, .signature = signature });
    }
}

fn enumerateTerminalGammaRankSplitEffects(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, dimension: u8, effects: *StructuralPrimitiveEffectBuffer) !void {
    var input_rank: u8 = 1;
    while (input_rank <= dimension) : (input_rank += 1) {
        if (profileSlot(start.form_profile, input_rank - 1) == 0) continue;
        const removed = profileDecrementedRank(start.form_profile, input_rank);
        var gamma_rank: u8 = 1;
        while (gamma_rank <= dimension) : (gamma_rank += 1) {
            var contractions: u8 = 0;
            while (contractions <= @min(input_rank, gamma_rank)) : (contractions += 1) {
                const action = makeExteriorGammaAction(spec.orthogonal_dimension, input_rank, gamma_rank, contractions, .none) orelse continue;
                if (action.output_rank == 0 or action.output_rank == input_rank) continue;
                var auxiliary_rank: u8 = 1;
                while (auxiliary_rank <= dimension) : (auxiliary_rank += 1) {
                    if (auxiliary_rank == input_rank or auxiliary_rank == action.output_rank) continue;
                    if (action.output_rank > auxiliary_rank) continue;
                    if (!spinorBilinearChiralityValid(start.chirality, spec.right.chirality, rankSplitBilinearParityRank(input_rank, action.output_rank, auxiliary_rank))) continue;
                    if (profileIncrementedRank(profileIncrementedRank(removed, action.output_rank), auxiliary_rank) != target.form_profile) continue;
                    const signature: PrimitiveSignature = .{
                        .kind = .gamma_rank_split,
                        .input_block = tensorFormRankBlock(spec.left.index, input_rank),
                        .output_block = tensorFormRankBlock(spec.output.index, action.output_rank),
                        .auxiliary_block = tensorFormRankBlock(spec.output.index, auxiliary_rank),
                        .action = action,
                        .tower_input_power = input_rank,
                        .tower_output_power = action.output_rank,
                        .tower_form_rank = auxiliary_rank,
                    };
                    try appendUniqueStructuralEffect(effects, .{ .kind = .gamma_rank_split, .next = target, .signature = signature });
                }
            }
        }
    }
}

fn appendUniqueStructuralEffect(effects: *StructuralPrimitiveEffectBuffer, effect: StructuralPrimitiveEffect) !void {
    var effect_index: u8 = 0;
    while (effect_index < effects.count) : (effect_index += 1) {
        const existing = effects.slots[effect_index];
        if (existing.kind == effect.kind and structuralSearchStateEql(existing.next, effect.next) and signatureEql(existing.signature, effect.signature)) return;
    }
    try effects.append(effect);
}

fn appendGammaProfileMoveEffects(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, effects: *StructuralPrimitiveEffectBuffer) !void {
    if (!(start.tower_power == target.tower_power or start.tower_power == target.tower_power + 1)) return;
    if (profileTotalPower(start.form_profile) != profileTotalPower(target.form_profile)) return;
    var source_index: u8 = 0;
    while (source_index < 32) : (source_index += 1) {
        if (profileSlot(start.form_profile, source_index) <= profileSlot(target.form_profile, source_index)) continue;
        const source_rank = source_index + 1;
        var target_index: u8 = 0;
        while (target_index < 32) : (target_index += 1) {
            if (profileSlot(start.form_profile, target_index) >= profileSlot(target.form_profile, target_index)) continue;
            const target_rank = target_index + 1;
            const moved_profile = profileIncrementedRank(profileDecrementedRank(start.form_profile, source_rank), target_rank);
            const action = firstExteriorGammaAction(spec.orthogonal_dimension, source_rank, target_rank, .none) orelse continue;
            const chirality_candidate: u8 = if (start.chirality != 0 and action.gamma_rank % 2 == 1) 3 - start.chirality else start.chirality;
            const next: StructuralSearchState = .{
                .form_profile = moved_profile,
                .tower_power = target.tower_power,
                .chirality = chirality_candidate,
                .has_spinor = true,
            };
            if (gammaProfileActionSignature(spec, start, next)) |signature| {
                try appendUniqueStructuralEffect(effects, .{ .kind = .gamma_wedge_shift, .next = next, .signature = signature });
            }
        }
    }
}

fn gammaInsertSignature(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState) ?PrimitiveSignature {
    if (!start.has_spinor or !spec.right.has_spinor or target.has_spinor) return null;
    if (spec.output.form_duality != .none) return null;
    if (start.tower_power != 0 or target.tower_power != 0) return null;
    const rank = inferTerminalGammaRank(start.form_profile, target.form_profile) orelse return null;
    if (rank == 0) return null;
    const action = makeExteriorGammaAction(spec.orthogonal_dimension, 0, rank, 0, .none) orelse return null;
    if (!spinorBilinearChiralityValid(start.chirality, spec.right.chirality, terminalProfileBilinearParityRank(start.form_profile, target.form_profile))) return null;
    return .{
        .kind = .gamma_insert,
        .input_block = spec.left.index,
        .output_block = tensorFormInsertedBlock(spec.output.index, rank),
        .action = action,
        .tower_output_power = action.output_rank,
    };
}

fn gammaWedgeShiftSignature(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState) ?PrimitiveSignature {
    if (spec.output.form_duality != .none) return null;
    if (!start.has_spinor or !spec.right.has_spinor or !target.has_spinor) return null;
    if (start.tower_power == 0 or start.tower_power != target.tower_power + 1) return null;
    if (start.chirality != target.chirality or spec.right.chirality != start.chirality) return null;
    if (profileTotalPower(start.form_profile) != profileTotalPower(target.form_profile)) return null;
    const transform = classifyProfileTransform(start.form_profile, target.form_profile);
    const inserted_rank = switch (transform.kind) {
        .shift_all_up, .move_rank_up => transform.target_rank - transform.source_rank,
        else => return null,
    };
    if (inserted_rank == 0) return null;
    const action = firstExteriorGammaAction(spec.orthogonal_dimension, transform.source_rank, transform.target_rank, .none) orelse return null;
    if (action.gamma_rank != inserted_rank or action.contraction_count != 0) return null;
    return .{
        .kind = .gamma_wedge_shift,
        .input_block = spec.left.index,
        .output_block = spec.output.index,
        .action = action,
        .tower_input_power = @intCast(start.tower_power),
        .tower_output_power = @intCast(target.tower_power),
    };
}

fn gammaProfileActionSignature(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState) ?PrimitiveSignature {
    if (spec.output.form_duality != .none) return null;
    if (!start.has_spinor or !spec.right.has_spinor or !target.has_spinor) return null;
    if (start.tower_power == 0) return null;
    if (!(start.tower_power == target.tower_power or start.tower_power == target.tower_power + 1)) return null;
    if (profileTotalPower(start.form_profile) != profileTotalPower(target.form_profile)) return null;
    const move = profileMovedAnyRank(start.form_profile, target.form_profile) orelse return null;
    const action = firstExteriorGammaAction(spec.orthogonal_dimension, move.source_rank, move.target_rank, .none) orelse return null;
    if (action.gamma_rank == 0) return null;
    if (!spinorActionChiralityValid(start.chirality, target.chirality, action.gamma_rank)) return null;
    return .{
        .kind = .gamma_wedge_shift,
        .input_block = spec.left.index,
        .output_block = spec.output.index,
        .action = action,
        .tower_input_power = @intCast(start.tower_power),
        .tower_output_power = @intCast(target.tower_power),
    };
}

fn gammaProfileAddRankSignature(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState) ?PrimitiveSignature {
    if (spec.output.form_duality != .none) return null;
    if (!start.has_spinor or !spec.right.has_spinor or !target.has_spinor) return null;
    if (start.tower_power == 0 or start.tower_power != target.tower_power) return null;
    if (profileTotalPower(target.form_profile) != profileTotalPower(start.form_profile) + 1) return null;
    var rank_index: u8 = 0;
    var inserted_rank: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const start_count = profileSlot(start.form_profile, rank_index);
        const target_count = profileSlot(target.form_profile, rank_index);
        if (target_count == start_count) continue;
        if (target_count != start_count + 1 or inserted_rank != 0) return null;
        inserted_rank = rank_index + 1;
    }
    if (inserted_rank == 0) return null;
    const action = makeExteriorGammaAction(spec.orthogonal_dimension, 0, inserted_rank, 0, .none) orelse return null;
    if (!spinorActionChiralityValid(start.chirality, target.chirality, action.gamma_rank)) return null;
    return .{
        .kind = .gamma_wedge_shift,
        .input_block = spec.left.index,
        .output_block = spec.output.index,
        .action = action,
        .tower_input_power = @intCast(start.tower_power),
        .tower_output_power = @intCast(target.tower_power),
    };
}

fn gammaRankSplitSignature(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState) ?PrimitiveSignature {
    if (!start.has_spinor or !spec.right.has_spinor or target.has_spinor) return null;
    if (spec.output.form_duality != .none) return null;
    if (start.tower_power != 0 or target.tower_power != 0) return null;
    const split = inferRankSplitProfile(start.form_profile, target.form_profile) orelse return null;
    const action = firstExteriorGammaAction(spec.orthogonal_dimension, split.source_rank, split.lower_rank, .none) orelse return null;
    if (!spinorBilinearChiralityValid(start.chirality, spec.right.chirality, rankSplitBilinearParityRank(split.source_rank, split.lower_rank, split.upper_rank))) return null;
    return .{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(spec.left.index, split.source_rank),
        .output_block = tensorFormRankBlock(spec.output.index, split.lower_rank),
        .auxiliary_block = tensorFormRankBlock(spec.output.index, split.upper_rank),
        .action = action,
        .tower_input_power = split.source_rank,
        .tower_output_power = split.lower_rank,
        .tower_form_rank = split.upper_rank,
    };
}

fn spinorTargetGammaRankSplitSignature(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState) ?PrimitiveSignature {
    if (!start.has_spinor or !spec.right.has_spinor or !target.has_spinor) return null;
    if (spec.output.form_duality != .none) return null;
    if (start.tower_power == 0 or start.tower_power != target.tower_power + 1) return null;
    const split = inferRankSplitProfile(start.form_profile, target.form_profile) orelse return null;
    const action = firstExteriorGammaAction(spec.orthogonal_dimension, split.source_rank, split.lower_rank, .none) orelse return null;
    return .{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(spec.left.index, split.source_rank),
        .output_block = tensorFormRankBlock(spec.output.index, split.lower_rank),
        .auxiliary_block = tensorFormRankBlock(spec.output.index, split.upper_rank),
        .action = action,
        .tower_input_power = @intCast(start.tower_power),
        .tower_output_power = @intCast(target.tower_power),
        .tower_form_rank = split.upper_rank,
    };
}

fn hodgeProjectSignature(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState) ?PrimitiveSignature {
    if (!start.has_spinor or !spec.right.has_spinor or target.has_spinor) return null;
    if (spec.output.form_duality == .none) return null;
    if (target.form_profile != 0 or spec.output.form_count != 1) return null;
    if (@as(u16, spec.output.form_rank) * 2 != spec.orthogonal_dimension) return null;
    const input_rank = profileOnlyRank(start.form_profile) orelse if (start.form_profile == 0) 0 else return null;
    if (input_rank >= spec.output.form_rank) return null;
    const action = firstExteriorGammaAction(spec.orthogonal_dimension, input_rank, spec.output.form_rank, spec.output.form_duality) orelse return null;
    if (action.contraction_count != 0) return null;
    if (!spinorBilinearChiralityValid(start.chirality, spec.right.chirality, terminalMiddleFormBilinearParityRank(start.form_profile, spec.output.form_rank))) return null;
    return .{
        .kind = .hodge_project,
        .input_block = tensorFormRankBlock(spec.left.index, input_rank),
        .output_block = tensorFormRankBlock(spec.output.index, spec.output.form_rank),
        .action = action,
        .tower_input_power = input_rank,
        .tower_output_power = action.output_rank,
        .normalization_tag = @intFromEnum(spec.output.form_duality),
    };
}

fn appendGammaWedgeShiftSignatureEffect(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, signature: PrimitiveSignature, word: *ProjectorCandidateWord) !bool {
    if (signature.kind != .gamma_wedge_shift or signature.action.dimension == 0) return false;
    try word.append(.{
        .kind = .gamma_wedge_shift,
        .input_block = signature.input_block,
        .output_block = signature.output_block,
        .rank = signature.action.gamma_rank,
        .output_rank = signature.action.output_rank,
        .auxiliary_rank = signature.action.input_rank,
        .action_gamma_rank = signature.action.gamma_rank,
        .action_contraction_count = signature.action.contraction_count,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = if (signature.action.contraction_count == 0) start.chirality else target.chirality,
        .duality = signature.action.duality,
    });
    return true;
}

fn appendSpinorTowerContractEffect(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, word: *ProjectorCandidateWord) !bool {
    if (spec.output.form_duality != .none) return false;
    if (!start.has_spinor or !spec.right.has_spinor or !target.has_spinor) return false;
    if (start.tower_power == 0) return false;
    if (start.tower_power > std.math.maxInt(u8) or target.tower_power > std.math.maxInt(u8)) return error.ProjectorProgramTooLarge;
    if (start.chirality != target.chirality) return false;
    if (start.tower_power != target.tower_power + 1) return false;

    const transform = classifyProfileTransform(start.form_profile, target.form_profile);
    const added_rank = switch (transform.kind) {
        .preserve => @as(u8, 0),
        .add_rank => transform.rank,
        else => return false,
    };
    try word.append(.{
        .kind = .spinor_tower_contract,
        .input_block = spec.left.index,
        .output_block = spec.output.index,
        .auxiliary_block = if (added_rank == 0) 0 else tensorFormRankBlock(spec.output.index, added_rank),
        .rank = @intCast(start.tower_power),
        .output_rank = @intCast(target.tower_power),
        .auxiliary_rank = added_rank,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = start.chirality,
    });
    return true;
}

fn appendGammaInsertSignatureEffect(spec: StructuralProjectorSpec, start: StructuralSearchState, signature: PrimitiveSignature, word: *ProjectorCandidateWord) !bool {
    if (signature.kind != .gamma_insert or signature.action.dimension == 0) return false;
    try word.append(.{
        .kind = .gamma_insert,
        .input_block = spec.left.index,
        .output_block = signature.output_block,
        .rank = signature.action.gamma_rank,
        .output_rank = signature.action.output_rank,
        .auxiliary_rank = signature.action.input_rank,
        .action_gamma_rank = signature.action.gamma_rank,
        .action_contraction_count = signature.action.contraction_count,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = start.chirality,
    });
    return true;
}

fn appendGammaRankSplitSignatureEffect(spec: StructuralProjectorSpec, start: StructuralSearchState, signature: PrimitiveSignature, word: *ProjectorCandidateWord) !bool {
    if (signature.kind != .gamma_rank_split or signature.action.dimension == 0) return false;
    try word.append(.{
        .kind = .gamma_rank_split,
        .input_block = signature.input_block,
        .output_block = signature.output_block,
        .auxiliary_block = signature.auxiliary_block,
        .rank = signature.action.input_rank,
        .output_rank = signature.action.output_rank,
        .auxiliary_rank = signature.tower_form_rank,
        .action_gamma_rank = signature.action.gamma_rank,
        .action_contraction_count = signature.action.contraction_count,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = start.chirality,
    });
    return true;
}

fn appendSpinorTowerContractAdjointEffect(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, word: *ProjectorCandidateWord) !bool {
    if (spec.output.form_duality != .none) return false;
    if (!start.has_spinor or !spec.right.has_spinor or !target.has_spinor) return false;
    if (target.tower_power == 0) return false;
    if (start.tower_power > std.math.maxInt(u8) or target.tower_power > std.math.maxInt(u8)) return error.ProjectorProgramTooLarge;
    if (target.tower_power != start.tower_power + 1) return false;
    const transform = classifyProfileTransform(start.form_profile, target.form_profile);
    const removed_rank = switch (transform.kind) {
        .preserve => blk: {
            if (start.chirality != target.chirality) return false;
            if (spec.right.chirality != start.chirality) return false;
            break :blk @as(u8, 0);
        },
        .remove_rank => blk: {
            if (!spinorActionChiralityValid(spec.right.chirality, target.chirality, transform.rank)) return false;
            break :blk transform.rank;
        },
        else => return false,
    };

    try word.append(.{
        .kind = .spinor_tower_contract_adjoint,
        .input_block = spec.left.index,
        .output_block = spec.output.index,
        .auxiliary_block = if (removed_rank == 0) 0 else tensorFormRankBlock(spec.left.index, removed_rank),
        .rank = @intCast(start.tower_power),
        .output_rank = @intCast(target.tower_power),
        .auxiliary_rank = removed_rank,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = start.chirality,
    });
    return true;
}

fn appendFormSpinorContractAdjointEffect(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, word: *ProjectorCandidateWord) !bool {
    if (spec.output.form_duality != .none) return false;
    if (start.has_spinor or !spec.right.has_spinor or !target.has_spinor) return false;
    if (start.tower_power != 0 or target.tower_power != 1) return false;
    if (target.tower_power > std.math.maxInt(u8)) return error.ProjectorProgramTooLarge;
    const transform = classifyProfileTransform(start.form_profile, target.form_profile);
    const removed_rank = switch (transform.kind) {
        .preserve => blk: {
            if (spec.right.chirality != target.chirality) return false;
            break :blk @as(u8, 0);
        },
        .remove_rank => blk: {
            if (!spinorActionChiralityValid(spec.right.chirality, target.chirality, transform.rank)) return false;
            break :blk transform.rank;
        },
        else => return false,
    };
    if (profileTotalPower(target.form_profile) + 1 > max_program_primitives) return false;

    try word.append(.{
        .kind = .spinor_tower_contract_adjoint,
        .input_block = spec.left.index,
        .output_block = spec.output.index,
        .auxiliary_block = if (removed_rank == 0) 0 else tensorFormRankBlock(spec.left.index, removed_rank),
        .rank = 0,
        .output_rank = @intCast(target.tower_power),
        .auxiliary_rank = removed_rank,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = target.chirality,
    });
    return true;
}

fn appendGammaInsertEffect(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, word: *ProjectorCandidateWord) !bool {
    if (!start.has_spinor or !spec.right.has_spinor or target.has_spinor) return false;
    if (spec.output.form_duality != .none) return false;
    if (start.tower_power != 0 or target.tower_power != 0) return false;
    const rank = inferTerminalGammaRank(start.form_profile, target.form_profile) orelse return false;
    if (rank == 0 or rank > spec.orthogonal_dimension) return false;
    const action = makeExteriorGammaAction(spec.orthogonal_dimension, 0, rank, 0, .none) orelse return false;
    if (!spinorBilinearChiralityValid(start.chirality, spec.right.chirality, terminalProfileBilinearParityRank(start.form_profile, target.form_profile))) return false;

    try word.append(.{
        .kind = .gamma_insert,
        .input_block = spec.left.index,
        .output_block = tensorFormInsertedBlock(spec.output.index, rank),
        .rank = action.gamma_rank,
        .output_rank = action.output_rank,
        .action_gamma_rank = action.gamma_rank,
        .action_contraction_count = action.contraction_count,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = start.chirality,
    });
    return true;
}

fn appendGammaWedgeShiftEffect(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, word: *ProjectorCandidateWord) !bool {
    if (spec.output.form_duality != .none) return false;
    if (!start.has_spinor or !spec.right.has_spinor or !target.has_spinor) return false;
    if (start.tower_power == 0 or start.tower_power != target.tower_power + 1) return false;
    if (start.chirality != target.chirality or spec.right.chirality != start.chirality) return false;
    if (profileTotalPower(start.form_profile) != profileTotalPower(target.form_profile)) return false;
    const transform = classifyProfileTransform(start.form_profile, target.form_profile);
    const inserted_rank = switch (transform.kind) {
        .shift_all_up, .move_rank_up => transform.target_rank - transform.source_rank,
        else => return false,
    };
    if (inserted_rank == 0 or inserted_rank > spec.orthogonal_dimension) return false;
    const action = firstExteriorGammaAction(spec.orthogonal_dimension, transform.source_rank, transform.target_rank, .none) orelse return false;
    if (action.gamma_rank != inserted_rank or action.contraction_count != 0) return false;

    try word.append(.{
        .kind = .gamma_wedge_shift,
        .input_block = spec.left.index,
        .output_block = spec.output.index,
        .rank = inserted_rank,
        .action_gamma_rank = action.gamma_rank,
        .action_contraction_count = action.contraction_count,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = start.chirality,
    });
    return true;
}

fn appendGammaRankSplitEffect(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, word: *ProjectorCandidateWord) !bool {
    if (!start.has_spinor or !spec.right.has_spinor or target.has_spinor) return false;
    if (spec.output.form_duality != .none) return false;
    if (start.tower_power != 0 or target.tower_power != 0) return false;
    const split = inferRankSplitProfile(start.form_profile, target.form_profile) orelse return false;
    const action = firstExteriorGammaAction(spec.orthogonal_dimension, split.source_rank, split.lower_rank, .none) orelse return false;
    if (!spinorBilinearChiralityValid(start.chirality, spec.right.chirality, rankSplitBilinearParityRank(split.source_rank, split.lower_rank, split.upper_rank))) return false;
    try word.append(.{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(spec.left.index, split.source_rank),
        .output_block = tensorFormRankBlock(spec.output.index, split.lower_rank),
        .auxiliary_block = tensorFormRankBlock(spec.output.index, split.upper_rank),
        .rank = split.source_rank,
        .output_rank = split.lower_rank,
        .auxiliary_rank = split.upper_rank,
        .action_gamma_rank = action.gamma_rank,
        .action_contraction_count = action.contraction_count,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = start.chirality,
    });
    return true;
}

fn appendHodgeProjectEffect(spec: StructuralProjectorSpec, start: StructuralSearchState, target: StructuralSearchState, word: *ProjectorCandidateWord) !bool {
    if (!start.has_spinor or !spec.right.has_spinor or target.has_spinor) return false;
    if (spec.output.form_duality == .none) return false;
    if (target.form_profile != 0 or spec.output.form_count != 1) return false;
    if (@as(u16, spec.output.form_rank) * 2 != spec.orthogonal_dimension) return false;
    const input_rank = profileOnlyRank(start.form_profile) orelse if (start.form_profile == 0) 0 else return false;
    if (input_rank >= spec.output.form_rank) return false;
    const action = firstExteriorGammaAction(spec.orthogonal_dimension, input_rank, spec.output.form_rank, spec.output.form_duality) orelse return false;
    if (action.contraction_count != 0) return false;
    if (!spinorBilinearChiralityValid(start.chirality, spec.right.chirality, terminalMiddleFormBilinearParityRank(start.form_profile, spec.output.form_rank))) return false;
    try word.append(.{
        .kind = .hodge_project,
        .input_block = tensorFormRankBlock(spec.left.index, input_rank),
        .output_block = tensorFormRankBlock(spec.output.index, spec.output.form_rank),
        .rank = action.gamma_rank,
        .output_rank = action.output_rank,
        .action_gamma_rank = action.gamma_rank,
        .action_contraction_count = action.contraction_count,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = start.chirality,
        .duality = spec.output.form_duality,
    });
    return true;
}

fn appendCarriedFormDelta(word: *ProjectorCandidateWord, input: rendering.IndexRef, output: rendering.IndexRef, carried_profile: u128, dimension: u16) !void {
    if (carried_profile == 0) return;
    try word.append(.{
        .kind = .form_delta,
        .input_block = tensorFormCarriedBlock(input),
        .output_block = tensorFormCarriedBlock(output),
        .orthogonal_dimension = dimension,
    });
}

fn appendFormProfileDeltas(word: *ProjectorCandidateWord, input: rendering.IndexRef, output: rendering.IndexRef, profile: u128, dimension: u16) !void {
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        var remaining = profileSlot(profile, rank_index);
        while (remaining != 0) : (remaining -= 1) {
            const rank = rank_index + 1;
            try word.append(.{
                .kind = .form_delta,
                .input_block = tensorFormRankBlock(input, rank),
                .output_block = tensorFormRankBlock(output, rank),
                .rank = rank,
                .orthogonal_dimension = dimension,
            });
        }
    }
}

fn spinorActionChiralityValid(input_chirality: u8, output_chirality: u8, form_rank: u8) bool {
    if (input_chirality == 0 or output_chirality == 0) return input_chirality == output_chirality;
    if (form_rank % 2 == 0) return input_chirality == output_chirality;
    return input_chirality != output_chirality;
}

fn spinorBilinearChiralityValid(left_chirality: u8, right_chirality: u8, form_rank: u8) bool {
    if (left_chirality == 0 or right_chirality == 0) return true;
    if (form_rank % 2 == 0) return left_chirality != right_chirality;
    return left_chirality == right_chirality;
}

fn rankSplitBilinearParityRank(source_rank: u8, lower_rank: u8, auxiliary_rank: u8) u8 {
    return source_rank +% lower_rank +% auxiliary_rank;
}

fn terminalProfileBilinearParityRank(input_profile: u128, output_profile: u128) u8 {
    return profileBilinearParityRank(input_profile) +% profileBilinearParityRank(output_profile);
}

fn terminalMiddleFormBilinearParityRank(input_profile: u128, output_rank: u8) u8 {
    return profileBilinearParityRank(input_profile) +% output_rank;
}

fn profileBilinearParityRank(profile: u128) u8 {
    var parity_rank: u8 = 0;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        if (profileSlot(profile, rank_index) % 2 == 0) continue;
        parity_rank +%= rank_index + 1;
    }
    return parity_rank;
}

fn spinorActionOutputChirality(input_chirality: u8, form_rank: u8) u8 {
    if (input_chirality == 0 or form_rank % 2 == 0) return input_chirality;
    return 3 - input_chirality;
}

fn makeExteriorGammaAction(dimension: u16, input_rank: u8, gamma_rank: u8, contraction_count: u8, duality: rendering.DualityTag) ?ExteriorGammaAction {
    if (dimension > std.math.maxInt(u8)) return null;
    if (input_rank > dimension or gamma_rank > dimension) return null;
    if (contraction_count > input_rank or contraction_count > gamma_rank) return null;
    const expanded_rank = @as(u16, input_rank) + gamma_rank;
    const removed_rank = @as(u16, contraction_count) * 2;
    if (removed_rank > expanded_rank) return null;
    const output_rank = expanded_rank - removed_rank;
    if (output_rank > dimension or output_rank > std.math.maxInt(u8)) return null;
    return .{
        .dimension = @intCast(dimension),
        .input_rank = input_rank,
        .gamma_rank = gamma_rank,
        .contraction_count = contraction_count,
        .output_rank = @intCast(output_rank),
        .chirality_parity = @intCast(gamma_rank & 1),
        .duality = duality,
    };
}

fn firstExteriorGammaAction(dimension: u16, input_rank: u8, output_rank: u8, duality: rendering.DualityTag) ?ExteriorGammaAction {
    if (dimension > std.math.maxInt(u8) or input_rank > dimension or output_rank > dimension) return null;
    var gamma_rank: u8 = 0;
    while (gamma_rank <= dimension) : (gamma_rank += 1) {
        var contractions: u8 = 0;
        while (contractions <= @min(input_rank, gamma_rank)) : (contractions += 1) {
            const action = makeExteriorGammaAction(dimension, input_rank, gamma_rank, contractions, duality) orelse continue;
            if (action.output_rank == output_rank) return action;
        }
        if (gamma_rank == std.math.maxInt(u8)) break;
    }
    return null;
}

fn exteriorGammaActionForTransition(dimension: u16, input_rank: u8, gamma_rank: u8, output_rank: u8, duality: rendering.DualityTag) ?ExteriorGammaAction {
    const expanded_rank = @as(u16, input_rank) + gamma_rank;
    if (expanded_rank < output_rank) return null;
    const removed_rank = expanded_rank - output_rank;
    if (removed_rank % 2 != 0) return null;
    if (removed_rank / 2 > std.math.maxInt(u8)) return null;
    return makeExteriorGammaAction(dimension, input_rank, gamma_rank, @intCast(removed_rank / 2), duality);
}

fn primitiveToSignature(slot: ProjectorPrimitive) ?PrimitiveSignature {
    const action_input_rank = primitiveExteriorInputRank(slot);
    const action_output_rank = primitiveExteriorOutputRank(slot);
    const action = switch (slot.kind) {
        .gamma_insert, .gamma_rank_split, .hodge_project => if (slot.action_gamma_rank != 0 or slot.action_contraction_count != 0)
            makeExteriorGammaAction(slot.orthogonal_dimension, action_input_rank, slot.action_gamma_rank, slot.action_contraction_count, slot.duality) orelse return null
        else switch (slot.kind) {
            .gamma_insert => exteriorGammaActionForTransition(slot.orthogonal_dimension, slot.auxiliary_rank, slot.rank, if (slot.output_rank == 0) slot.rank else slot.output_rank, slot.duality) orelse return null,
            .gamma_rank_split => firstExteriorGammaAction(slot.orthogonal_dimension, slot.rank, slot.output_rank, slot.duality) orelse return null,
            .hodge_project => firstExteriorGammaAction(slot.orthogonal_dimension, slot.output_rank - slot.rank, slot.output_rank, slot.duality) orelse return null,
            else => unreachable,
        },
        .gamma_wedge_shift => if (slot.action_gamma_rank != 0 or slot.action_contraction_count != 0)
            makeExteriorGammaAction(slot.orthogonal_dimension, action_input_rank, slot.action_gamma_rank, slot.action_contraction_count, slot.duality) orelse return null
        else
            firstExteriorGammaAction(slot.orthogonal_dimension, 0, slot.rank, slot.duality) orelse return null,
        else => ExteriorGammaAction{},
    };
    if (action.output_rank != action_output_rank and action.dimension != 0) return null;
    return .{
        .kind = slot.kind,
        .input_block = slot.input_block,
        .output_block = slot.output_block,
        .auxiliary_block = slot.auxiliary_block,
        .action = action,
        .tower_input_power = slot.rank,
        .tower_output_power = slot.output_rank,
        .tower_form_rank = slot.auxiliary_rank,
        .normalization_tag = @intFromEnum(slot.duality),
    };
}

fn primitiveExteriorInputRank(slot: ProjectorPrimitive) u8 {
    return switch (slot.kind) {
        .gamma_insert => slot.auxiliary_rank,
        .gamma_wedge_shift => if (slot.action_gamma_rank != 0 or slot.action_contraction_count != 0) slot.auxiliary_rank else 0,
        .gamma_rank_split => slot.rank,
        .hodge_project => slot.output_rank - slot.rank,
        else => 0,
    };
}

fn primitiveExteriorOutputRank(slot: ProjectorPrimitive) u8 {
    return switch (slot.kind) {
        .gamma_insert => if (slot.output_rank == 0) slot.rank else slot.output_rank,
        .gamma_wedge_shift => if (slot.action_gamma_rank != 0 or slot.action_contraction_count != 0) slot.output_rank else slot.rank,
        .gamma_rank_split, .hodge_project => slot.output_rank,
        else => 0,
    };
}

fn signatureEql(left: PrimitiveSignature, right: PrimitiveSignature) bool {
    return left.kind == right.kind and
        left.input_block == right.input_block and
        left.output_block == right.output_block and
        left.auxiliary_block == right.auxiliary_block and
        left.action.dimension == right.action.dimension and
        left.action.input_rank == right.action.input_rank and
        left.action.gamma_rank == right.action.gamma_rank and
        left.action.contraction_count == right.action.contraction_count and
        left.action.output_rank == right.action.output_rank and
        left.action.chirality_parity == right.action.chirality_parity and
        left.action.duality == right.action.duality and
        left.tower_input_power == right.tower_input_power and
        left.tower_output_power == right.tower_output_power and
        left.tower_form_rank == right.tower_form_rank and
        left.normalization_tag == right.normalization_tag;
}

fn signatureChiralityValid(input_chirality: u8, output_chirality: u8, signature: PrimitiveSignature) bool {
    return switch (signature.kind) {
        .gamma_insert, .gamma_action, .gamma_wedge_shift, .gamma_trace, .gamma_rank_split, .hodge_project => spinorActionChiralityValid(input_chirality, output_chirality, signature.action.gamma_rank),
        else => input_chirality == output_chirality or input_chirality == 0 or output_chirality == 0,
    };
}

fn signatureProfileTransition(input_profile: u128, output_profile: u128, signature: PrimitiveSignature) bool {
    if (signature.action.dimension == 0) return input_profile == output_profile;
    var profile = input_profile;
    if (signature.action.input_rank != 0) {
        const input_index = signature.action.input_rank - 1;
        if (profileSlot(profile, input_index) == 0) return false;
        profile -= @as(u128, 1) << @intCast(input_index * 4);
    }
    if (signature.action.output_rank != 0) {
        const output_index = signature.action.output_rank - 1;
        if (profileSlot(profile, output_index) == 0xf) return false;
        profile += @as(u128, 1) << @intCast(output_index * 4);
    }
    return profile == output_profile;
}

fn structuralCandidateInnerProduct(left: ProjectorCandidateWord, right: ProjectorCandidateWord) !Rational {
    if (left.count == 0 or right.count == 0) return Rational.zero();
    if (left.count > right.count) return Rational.zero();

    var used = [_]bool{false} ** max_program_primitives;
    var acc: ContractionAccumulator = .{};
    var left_index: u8 = 0;
    while (left_index < left.count) : (left_index += 1) {
        var matched = false;
        var saw_zero = false;
        var saw_unsupported = false;
        var right_index: u8 = 0;
        while (right_index < right.count) : (right_index += 1) {
            if (used[right_index]) continue;
            const factor = structuralPrimitiveContraction(left.slots[left_index], right.slots[right_index]) catch {
                saw_unsupported = true;
                continue;
            };
            if (factor.numerator == 0) {
                saw_zero = true;
                continue;
            }
            acc.coefficient = try acc.coefficient.mul(factor);
            used[right_index] = true;
            matched = true;
            break;
        }
        if (!matched) {
            if (saw_zero) return Rational.zero();
            if (saw_unsupported) return error.UnsupportedContraction;
            return Rational.zero();
        }
    }

    var right_index: u8 = 0;
    while (right_index < right.count) : (right_index += 1) {
        if (!used[right_index]) return Rational.zero();
    }
    return if (acc.is_zero) Rational.zero() else acc.coefficient;
}

fn structuralPrimitiveContraction(left: ProjectorPrimitive, right: ProjectorPrimitive) !Rational {
    if (left.kind == .form_delta and right.kind == .form_delta) return try formDeltaContraction(left, right);
    if (left.kind == .form_delta and isExteriorGammaPrimitive(right.kind)) return try formDeltaExteriorGammaContraction(left, right);
    if (isExteriorGammaPrimitive(left.kind) and right.kind == .form_delta) return try formDeltaExteriorGammaContraction(right, left);
    if (isExteriorGammaPrimitive(left.kind) and isExteriorGammaPrimitive(right.kind)) return exteriorGammaContraction(left, right);
    if (isSpinorTowerPrimitive(left.kind) and isSpinorTowerPrimitive(right.kind)) return try spinorTowerContraction(left, right);
    if (left.kind == .vector_spinor_identity or left.kind == .gamma_trace or right.kind == .vector_spinor_identity or right.kind == .gamma_trace) return error.UnsupportedContraction;
    return error.UnsupportedContraction;
}

fn formDeltaContraction(left: ProjectorPrimitive, right: ProjectorPrimitive) !Rational {
    const left_input_rank = tensorFormBlockRank(left.input_block);
    const right_input_rank = tensorFormBlockRank(right.input_block);
    if (left_input_rank != null and right_input_rank != null and left_input_rank.? != right_input_rank.?) return Rational.zero();
    const left_output_rank = tensorFormBlockRank(left.output_block);
    const right_output_rank = tensorFormBlockRank(right.output_block);
    if (left_output_rank != null and right_output_rank != null and left_output_rank.? != right_output_rank.?) return Rational.zero();
    const rank = formDeltaContractionRank(left, right, left_input_rank, left_output_rank, right_input_rank, right_output_rank) orelse return Rational.one();
    const dimension = formDeltaContractionDimension(left, right) orelse return Rational.one();
    if (rank > dimension) return Rational.zero();
    return Rational.init(try binomialI64Wide(dimension, rank), 1);
}

fn formDeltaContractionRank(left: ProjectorPrimitive, right: ProjectorPrimitive, left_input_rank: ?u8, left_output_rank: ?u8, right_input_rank: ?u8, right_output_rank: ?u8) ?u8 {
    var rank: u8 = 0;
    if (!mergeFormDeltaRank(&rank, left_input_rank)) return null;
    if (!mergeFormDeltaRank(&rank, left_output_rank)) return null;
    if (!mergeFormDeltaRank(&rank, right_input_rank)) return null;
    if (!mergeFormDeltaRank(&rank, right_output_rank)) return null;
    if (left.rank != 0 and !mergeFormDeltaRank(&rank, left.rank)) return null;
    if (right.rank != 0 and !mergeFormDeltaRank(&rank, right.rank)) return null;
    return if (rank == 0) null else rank;
}

fn mergeFormDeltaRank(rank: *u8, candidate: ?u8) bool {
    const value = candidate orelse return true;
    if (rank.* == 0) {
        rank.* = value;
        return true;
    }
    return rank.* == value;
}

fn formDeltaContractionDimension(left: ProjectorPrimitive, right: ProjectorPrimitive) ?u16 {
    if (left.orthogonal_dimension == 0 and right.orthogonal_dimension == 0) return null;
    if (left.orthogonal_dimension == 0) return right.orthogonal_dimension;
    if (right.orthogonal_dimension == 0) return left.orthogonal_dimension;
    if (left.orthogonal_dimension != right.orthogonal_dimension) return 0;
    return left.orthogonal_dimension;
}

fn formDeltaExteriorGammaContraction(delta: ProjectorPrimitive, gamma: ProjectorPrimitive) !Rational {
    const delta_input_rank = tensorFormBlockRank(delta.input_block);
    const delta_output_rank = tensorFormBlockRank(delta.output_block);
    const rank = formDeltaContractionRank(delta, delta, delta_input_rank, delta_output_rank, delta_input_rank, delta_output_rank) orelse return error.UnsupportedContraction;
    const signature = primitiveToSignature(gamma) orelse return error.UnsupportedContraction;
    if (delta.orthogonal_dimension != 0 and signature.action.dimension != 0 and delta.orthogonal_dimension != signature.action.dimension) return Rational.zero();
    if (signature.action.input_rank != rank or signature.action.output_rank != rank) return Rational.zero();
    if (signature.action.duality != .none) return Rational.zero();
    if (signature.action.gamma_rank != 0 or signature.action.contraction_count != 0) return Rational.zero();
    const dimension = if (delta.orthogonal_dimension != 0) delta.orthogonal_dimension else @as(u16, signature.action.dimension);
    if (dimension == 0) return Rational.one();
    if (rank > dimension) return Rational.zero();
    return Rational.init(try binomialI64Wide(dimension, rank), 1);
}

fn exteriorGammaContraction(left: ProjectorPrimitive, right: ProjectorPrimitive) !Rational {
    if (left.orthogonal_dimension != right.orthogonal_dimension) return Rational.zero();
    if (left.chirality != 0 and right.chirality != 0 and left.chirality != right.chirality) return Rational.zero();
    const left_signature = primitiveToSignature(left) orelse return error.UnsupportedContraction;
    const right_signature = primitiveToSignature(right) orelse return error.UnsupportedContraction;
    if (left_signature.action.dimension != right_signature.action.dimension) return Rational.zero();
    if (left_signature.action.input_rank != right_signature.action.input_rank) return Rational.zero();
    if (left_signature.action.output_rank != right_signature.action.output_rank) return Rational.zero();
    if (left_signature.action.chirality_parity != right_signature.action.chirality_parity) return Rational.zero();
    if (left_signature.kind == .hodge_project or right_signature.kind == .hodge_project) {
        return hodgeExteriorGammaContraction(left_signature, right_signature);
    }
    if (left_signature.action.duality != right_signature.action.duality) return Rational.zero();
    return Rational.init(try exteriorGammaActionProductCoefficient(left_signature.action, right_signature.action), 1);
}

fn hodgeExteriorGammaContraction(left: PrimitiveSignature, right: PrimitiveSignature) Rational {
    if (left.action.gamma_rank != right.action.gamma_rank) return Rational.zero();
    if (left.action.contraction_count != right.action.contraction_count) return Rational.zero();
    if (left.kind == .hodge_project and right.kind == .hodge_project) {
        return if (left.action.duality == right.action.duality) Rational.one() else Rational.zero();
    }

    const hodge = if (left.kind == .hodge_project) left else right;
    const other = if (left.kind == .hodge_project) right else left;
    if (hodge.action.duality == .none or other.action.duality != .none) return Rational.zero();
    if (@as(u16, hodge.action.output_rank) * 2 != hodge.action.dimension) return Rational.zero();
    return Rational.one();
}

fn spinorTowerContraction(left: ProjectorPrimitive, right: ProjectorPrimitive) !Rational {
    if (left.orthogonal_dimension != right.orthogonal_dimension) return Rational.zero();
    if (left.chirality != 0 and right.chirality != 0 and left.chirality != right.chirality) return Rational.zero();
    if (left.rank != right.rank or left.output_rank != right.output_rank) return Rational.zero();
    if (left.auxiliary_rank != right.auxiliary_rank) return Rational.zero();
    if (left.kind != right.kind) return Rational.zero();
    return Rational.init(try spinorTowerPrimitiveNorm(left), 1);
}

fn isExteriorGammaPrimitive(kind: ProjectorPrimitiveKind) bool {
    return switch (kind) {
        .gamma_insert, .gamma_action, .gamma_wedge_shift, .gamma_rank_split, .hodge_project => true,
        else => false,
    };
}

fn isSpinorTowerPrimitive(kind: ProjectorPrimitiveKind) bool {
    return switch (kind) {
        .spinor_tower_contract, .spinor_tower_contract_adjoint => true,
        else => false,
    };
}

fn spinorTowerPrimitiveNorm(slot: ProjectorPrimitive) !i64 {
    const base = switch (slot.kind) {
        .spinor_tower_contract => blk: {
            if (slot.rank == 0 or slot.rank != slot.output_rank + 1) return error.UnsupportedContraction;
            break :blk @as(i64, slot.rank);
        },
        .spinor_tower_contract_adjoint => blk: {
            if (slot.output_rank != slot.rank + 1) return error.UnsupportedContraction;
            break :blk try checkedAddI64(try spinorModuleDimensionI64(slot.orthogonal_dimension), slot.rank);
        },
        else => return error.UnsupportedContraction,
    };
    return base;
}

fn spinorModuleDimensionI64(dimension: u16) !i64 {
    if (dimension == 0) return error.UnsupportedContraction;
    const exponent: u16 = if (dimension % 2 == 0) blk: {
        if (dimension < 2) return error.UnsupportedContraction;
        break :blk dimension / 2 - 1;
    } else dimension / 2;
    if (exponent >= 62) return error.GramIntegerOverflow;
    return @as(i64, 1) << @intCast(exponent);
}

fn exteriorGammaActionProductCoefficient(left: ExteriorGammaAction, right: ExteriorGammaAction) !i64 {
    if (left.gamma_rank != right.gamma_rank) return error.UnsupportedContraction;
    if (left.contraction_count != right.contraction_count) return error.UnsupportedContraction;
    return gammaProductCoefficientSmall(left.gamma_rank, right.gamma_rank, left.contraction_count);
}

fn gammaProductCoefficientSmall(left_rank: u8, right_rank: u8, contractions: u8) !i64 {
    var coefficient: i64 = 1;
    coefficient = try checkedMulI64(coefficient, try binomialI64(left_rank, contractions));
    coefficient = try checkedMulI64(coefficient, try binomialI64(right_rank, contractions));
    coefficient = try checkedMulI64(coefficient, try factorialI64(contractions));
    const contraction_pairs = if (contractions < 2) 0 else @as(u16, contractions) * (@as(u16, contractions) - 1) / 2;
    if (contraction_pairs % 2 == 1) coefficient = try checkedNegI64(coefficient);
    return coefficient;
}

fn binomialI64(n: u8, k: u8) !i64 {
    return binomialI64Wide(n, k);
}

fn binomialI64Wide(n: u16, k: u8) !i64 {
    if (k > n) return 0;
    const wide_k: u16 = k;
    const choose = @min(wide_k, n - wide_k);
    var result: i64 = 1;
    var divisor: u16 = 1;
    while (divisor <= choose) : (divisor += 1) {
        const numerator = n - choose + divisor;
        result = try checkedMulI64(result, numerator);
        result = @divExact(result, divisor);
    }
    return result;
}

fn factorialI64(n: u8) !i64 {
    if (n < 2) return 1;
    var result: i64 = 1;
    var factor: u8 = 2;
    while (factor <= n) : (factor += 1) {
        result = try checkedMulI64(result, factor);
    }
    return result;
}

fn projectorProgramTermCount(program: ProjectorProgram) u16 {
    var count: u16 = 0;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            if (program.inverse_gram[@as(usize, row) * program.pivot_count + column].numerator != 0) count += 1;
        }
    }
    return count;
}

fn projectorProgramTermAt(program: ProjectorProgram, term_index: u16) !ProjectorProgramTerm {
    var seen: u16 = 0;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
            if (coefficient.numerator == 0) continue;
            if (seen == term_index) {
                return .{
                    .left_candidate = program.pivots[row],
                    .right_candidate = program.pivots[column],
                    .coefficient = coefficient,
                };
            }
            seen += 1;
        }
    }
    return error.ProjectorConstructorTermOutOfBounds;
}

fn projectorPrimitiveEql(left: ProjectorPrimitive, right: ProjectorPrimitive) bool {
    return left.kind == right.kind and
        left.input_block == right.input_block and
        left.output_block == right.output_block and
        left.auxiliary_block == right.auxiliary_block and
        left.rank == right.rank and
        left.output_rank == right.output_rank and
        left.auxiliary_rank == right.auxiliary_rank and
        left.orthogonal_dimension == right.orthogonal_dimension and
        left.chirality == right.chirality and
        left.duality == right.duality;
}

fn invertSmallGram(dimension: u8, entries: []const Rational) ![max_program_gram_entries]Rational {
    if (dimension > max_program_pivots) return error.UnsupportedTensorPivotCap;
    const width: usize = dimension;
    if (entries.len < width * width) return error.InvalidGramMatrixSize;

    var matrix: [max_program_pivots * max_program_pivots * 2]Rational = [_]Rational{Rational.zero()} ** (max_program_pivots * max_program_pivots * 2);
    var row: usize = 0;
    while (row < width) : (row += 1) {
        var column: usize = 0;
        while (column < width) : (column += 1) {
            matrix[row * max_program_pivots * 2 + column] = entries[row * width + column];
            matrix[row * max_program_pivots * 2 + width + column] = if (row == column) Rational.one() else Rational.zero();
        }
    }

    var pivot_row: usize = 0;
    while (pivot_row < width) : (pivot_row += 1) {
        const source_row = findAugmentedPivotRow(matrix[0..], width, pivot_row) orelse return error.SingularGramMatrix;
        if (source_row != pivot_row) swapAugmentedRows(matrix[0..], width, pivot_row, source_row);

        const pivot = matrix[pivot_row * max_program_pivots * 2 + pivot_row];
        var column: usize = 0;
        while (column < width * 2) : (column += 1) {
            matrix[pivot_row * max_program_pivots * 2 + column] = try matrix[pivot_row * max_program_pivots * 2 + column].div(pivot);
        }

        row = 0;
        while (row < width) : (row += 1) {
            if (row == pivot_row) continue;
            const factor = matrix[row * max_program_pivots * 2 + pivot_row];
            if (factor.numerator == 0) continue;
            column = 0;
            while (column < width * 2) : (column += 1) {
                const scaled = try factor.mul(matrix[pivot_row * max_program_pivots * 2 + column]);
                matrix[row * max_program_pivots * 2 + column] = try matrix[row * max_program_pivots * 2 + column].sub(scaled);
            }
        }
    }

    var inverse: [max_program_gram_entries]Rational = [_]Rational{Rational.zero()} ** max_program_gram_entries;
    row = 0;
    while (row < width) : (row += 1) {
        var column: usize = 0;
        while (column < width) : (column += 1) {
            inverse[row * width + column] = matrix[row * max_program_pivots * 2 + width + column];
        }
    }
    return inverse;
}

fn findAugmentedPivotRow(matrix: []const Rational, width: usize, first_row: usize) ?usize {
    var row = first_row;
    while (row < width) : (row += 1) {
        if (matrix[row * max_program_pivots * 2 + first_row].numerator != 0) return row;
    }
    return null;
}

fn swapAugmentedRows(matrix: []Rational, width: usize, left: usize, right: usize) void {
    var column: usize = 0;
    while (column < width * 2) : (column += 1) {
        const left_index = left * max_program_pivots * 2 + column;
        const right_index = right * max_program_pivots * 2 + column;
        const temporary = matrix[left_index];
        matrix[left_index] = matrix[right_index];
        matrix[right_index] = temporary;
    }
}

fn appendStructuralProjectorProgramTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: StructuralProjectorSpec, program: ProjectorProgram, term_index: u16) !rendering.RationalId {
    const term = try projectorProgramTermAt(program, term_index);
    try appendStructuralCandidateWordAtoms(allocator, atoms, spec, program.candidates[term.left_candidate]);
    try appendStructuralCandidateWordAdjointAtoms(allocator, atoms, spec, program.candidates[term.right_candidate]);
    return rationalToRenderingId(term.coefficient);
}

fn appendProjectorProgramTermAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorFormProjectionSpec, program: ProjectorProgram, term_index: u16) !rendering.RationalId {
    const term = try projectorProgramTermAt(program, term_index);
    try appendCandidateWordAtoms(allocator, atoms, spec, program.candidates[term.left_candidate]);
    try appendCandidateWordAdjointAtoms(allocator, atoms, spec, program.candidates[term.right_candidate]);
    return rationalToRenderingId(term.coefficient);
}

fn appendTensorSpinorCandidateWordAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorSpinorProjectionSpec, word: ProjectorCandidateWord) !void {
    var slot_index: u8 = 0;
    while (slot_index < word.count) : (slot_index += 1) {
        const slot = word.slots[slot_index];
        switch (slot.kind) {
            .spinor_tower_contract => try appendSpinorTowerContractAtoms(allocator, atoms, spec.operator_id, spec.left, spec.right, spec.output, slot.auxiliary_block, spec.orthogonal_dimension, slot.rank, slot.output_rank, slot.auxiliary_rank, spec.chirality),
            else => return error.UnsupportedTensorSpinorProjectionTerm,
        }
    }
}

fn appendTensorSpinorCandidateWordAdjointAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorSpinorProjectionSpec, word: ProjectorCandidateWord) !void {
    var remaining = word.count;
    while (remaining != 0) {
        remaining -= 1;
        const slot = word.slots[remaining];
        switch (slot.kind) {
            .spinor_tower_contract => try appendSpinorTowerContractAdjointAtoms(allocator, atoms, spec.operator_id, spec.output, spec.right, spec.left, slot.auxiliary_block, spec.orthogonal_dimension, slot.output_rank, slot.rank, slot.auxiliary_rank, spec.chirality),
            else => return error.UnsupportedProjectorAdjointTerm,
        }
    }
}

fn appendExteriorGammaActionAtom(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), operator_id: u32, input_index: rendering.IndexRef, right_index: rendering.IndexRef, output_index: rendering.IndexRef, slot: ProjectorPrimitive) !void {
    const input_rank = primitiveExteriorInputRank(slot);
    const output_rank = primitiveExteriorOutputRank(slot);
    const gamma_rank = if (slot.action_gamma_rank != 0 or slot.action_contraction_count != 0) slot.action_gamma_rank else slot.rank;
    try atoms.append(allocator, .{ .exterior_gamma_action = .{
        .operator_id = operator_id,
        .input_form = if (slot.input_block == 0) tensorFormRankBlock(input_index, input_rank) else slot.input_block,
        .gamma_form = if (slot.auxiliary_block == 0) tensorFormRankBlock(output_index, gamma_rank) else slot.auxiliary_block,
        .output_form = if (slot.output_block == 0) tensorFormRankBlock(output_index, output_rank) else slot.output_block,
        .spinor_input = right_index,
        .spinor_output = tensorSpinorSpinorIndex(output_index),
        .orthogonal_dimension = slot.orthogonal_dimension,
        .input_rank = input_rank,
        .gamma_rank = gamma_rank,
        .output_rank = output_rank,
        .contraction_count = slot.action_contraction_count,
        .chirality = slot.chirality,
        .duality = slot.duality,
    } });
}

fn appendSpinorTowerContractAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), operator_id: u32, input_tower: rendering.IndexRef, spinor: rendering.IndexRef, output_tower: rendering.IndexRef, output_form: rendering.IndexBlockId, dimension: u16, input_power: u16, output_power: u16, form_rank: u8, chirality: u8) !void {
    var slot: u16 = 0;
    while (slot < output_power) : (slot += 1) {
        try atoms.append(allocator, .{ .spinor_index_delta = .{
            .operator_id = operator_id,
            .source_tower = input_tower,
            .output_tower = output_tower,
            .source_slot = slot,
            .output_slot = slot,
            .chirality = chirality,
        } });
    }
    try atoms.append(allocator, .{ .gamma_form = .{
        .operator_id = operator_id,
        .spinor_left = input_tower,
        .spinor_right = spinor,
        .form = output_form,
        .orthogonal_dimension = dimension,
        .rank = form_rank,
        .chirality = chirality,
    } });
    _ = input_power;
}

fn appendSpinorTowerContractAdjointAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), operator_id: u32, input_tower: rendering.IndexRef, spinor: rendering.IndexRef, output_tower: rendering.IndexRef, input_form: rendering.IndexBlockId, dimension: u16, input_power: u16, output_power: u16, form_rank: u8, chirality: u8) !void {
    var slot: u16 = 0;
    while (slot < input_power) : (slot += 1) {
        try atoms.append(allocator, .{ .spinor_index_delta = .{
            .operator_id = operator_id,
            .source_tower = input_tower,
            .output_tower = output_tower,
            .source_slot = slot,
            .output_slot = slot,
            .chirality = chirality,
        } });
    }
    try atoms.append(allocator, .{ .gamma_action = .{
        .operator_id = operator_id,
        .form = input_form,
        .spinor_input = spinor,
        .spinor_output = output_tower,
        .orthogonal_dimension = dimension,
        .rank = form_rank,
        .chirality = chirality,
    } });
    _ = output_power;
}

fn appendGammaRankSplitAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), operator_id: u32, spinor_left: rendering.IndexRef, spinor_right: rendering.IndexRef, input_form: rendering.IndexBlockId, lower_form: rendering.IndexBlockId, upper_form: rendering.IndexBlockId, dimension: u16, source_rank: u8, lower_rank: u8, upper_rank: u8, chirality: u8) !void {
    try atoms.append(allocator, .{ .form_rank_split_delta = .{
        .source_form = input_form,
        .lower_form = lower_form,
        .upper_form = upper_form,
        .source_rank = source_rank,
        .lower_rank = lower_rank,
        .upper_rank = upper_rank,
    } });
    try atoms.append(allocator, .{ .gamma_form = .{
        .operator_id = operator_id,
        .spinor_left = spinor_left,
        .spinor_right = spinor_right,
        .form = upper_form,
        .orthogonal_dimension = dimension,
        .rank = upper_rank,
        .chirality = chirality,
    } });
}

fn appendGammaRankSplitAdjointAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), operator_id: u32, spinor_input: rendering.IndexRef, spinor_output: rendering.IndexRef, input_lower_form: rendering.IndexBlockId, input_upper_form: rendering.IndexBlockId, output_form: rendering.IndexBlockId, dimension: u16, source_rank: u8, lower_rank: u8, upper_rank: u8, chirality: u8) !void {
    try atoms.append(allocator, .{ .form_rank_split_delta = .{
        .source_form = output_form,
        .lower_form = input_lower_form,
        .upper_form = input_upper_form,
        .source_rank = source_rank,
        .lower_rank = lower_rank,
        .upper_rank = upper_rank,
    } });
    try atoms.append(allocator, .{ .gamma_action = .{
        .operator_id = operator_id,
        .form = input_upper_form,
        .spinor_input = spinor_input,
        .spinor_output = spinor_output,
        .orthogonal_dimension = dimension,
        .rank = upper_rank,
        .chirality = chirality,
    } });
}

fn appendStructuralCandidateWordAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: StructuralProjectorSpec, word: ProjectorCandidateWord) !void {
    var slot_index: u8 = 0;
    while (slot_index < word.count) : (slot_index += 1) {
        const slot = word.slots[slot_index];
        switch (slot.kind) {
            .spinor_tower_contract => try appendSpinorTowerContractAtoms(allocator, atoms, spec.operator_id, spec.left.index, spec.right.index, spec.output.index, slot.auxiliary_block, spec.orthogonal_dimension, slot.rank, slot.output_rank, slot.auxiliary_rank, slot.chirality),
            .spinor_tower_contract_adjoint => try appendSpinorTowerContractAdjointAtoms(allocator, atoms, spec.operator_id, spec.left.index, spec.right.index, spec.output.index, slot.auxiliary_block, spec.orthogonal_dimension, slot.rank, slot.output_rank, slot.auxiliary_rank, slot.chirality),
            .gamma_insert => try atoms.append(allocator, .{ .gamma_form = .{
                .operator_id = spec.operator_id,
                .spinor_left = tensorSpinorSpinorIndex(spec.left.index),
                .spinor_right = spec.right.index,
                .form = slot.output_block,
                .orthogonal_dimension = spec.orthogonal_dimension,
                .rank = slot.rank,
                .chirality = slot.chirality,
            } }),
            .gamma_wedge_shift => try appendExteriorGammaActionAtom(allocator, atoms, spec.operator_id, spec.left.index, spec.right.index, spec.output.index, slot),
            .gamma_rank_split => try appendGammaRankSplitAtoms(
                allocator,
                atoms,
                spec.operator_id,
                tensorSpinorSpinorIndex(spec.left.index),
                spec.right.index,
                tensorFormRankBlock(spec.left.index, slot.rank),
                tensorFormRankBlock(spec.output.index, slot.output_rank),
                tensorFormRankBlock(spec.output.index, slot.auxiliary_rank),
                spec.orthogonal_dimension,
                slot.rank,
                slot.output_rank,
                slot.auxiliary_rank,
                slot.chirality,
            ),
            .form_delta => try atoms.append(allocator, .{ .generalized_delta = .{
                .upper = if (slot.input_block == 0) tensorFormCarriedBlock(spec.left.index) else slot.input_block,
                .lower = if (slot.output_block == 0) tensorFormCarriedBlock(spec.output.index) else slot.output_block,
            } }),
            .hodge_project => try appendExteriorGammaActionAtom(allocator, atoms, spec.operator_id, spec.left.index, spec.right.index, spec.output.index, slot),
            else => return error.UnsupportedStructuralProjectorTerm,
        }
    }
}

fn appendStructuralCandidateWordAdjointAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: StructuralProjectorSpec, word: ProjectorCandidateWord) !void {
    var remaining = word.count;
    while (remaining != 0) {
        remaining -= 1;
        const slot = word.slots[remaining];
        switch (slot.kind) {
            .spinor_tower_contract => try appendSpinorTowerContractAdjointAtoms(allocator, atoms, spec.operator_id, spec.output.index, spec.right.index, spec.left.index, slot.auxiliary_block, spec.orthogonal_dimension, slot.output_rank, slot.rank, slot.auxiliary_rank, slot.chirality),
            .spinor_tower_contract_adjoint => try appendSpinorTowerContractAtoms(allocator, atoms, spec.operator_id, spec.output.index, spec.right.index, spec.left.index, slot.auxiliary_block, spec.orthogonal_dimension, slot.output_rank, slot.rank, slot.auxiliary_rank, slot.chirality),
            .form_delta => try atoms.append(allocator, .{ .generalized_delta = .{
                .upper = if (slot.output_block == 0) tensorFormCarriedBlock(spec.output.index) else slot.output_block,
                .lower = if (slot.input_block == 0) tensorFormCarriedBlock(spec.left.index) else slot.input_block,
            } }),
            .gamma_insert => try atoms.append(allocator, .{ .gamma_action = .{
                .operator_id = spec.operator_id,
                .form = slot.output_block,
                .spinor_input = spec.right.index,
                .spinor_output = tensorSpinorSpinorIndex(spec.left.index),
                .orthogonal_dimension = spec.orthogonal_dimension,
                .rank = slot.rank,
                .chirality = slot.chirality,
            } }),
            .gamma_wedge_shift => try appendExteriorGammaActionAtom(allocator, atoms, spec.operator_id, spec.output.index, spec.right.index, spec.left.index, slot),
            .hodge_project => try appendExteriorGammaActionAtom(allocator, atoms, spec.operator_id, spec.output.index, spec.right.index, spec.left.index, slot),
            .gamma_rank_split => try appendGammaRankSplitAdjointAtoms(
                allocator,
                atoms,
                spec.operator_id,
                spec.right.index,
                tensorSpinorSpinorIndex(spec.left.index),
                tensorFormRankBlock(spec.output.index, slot.output_rank),
                tensorFormRankBlock(spec.output.index, slot.auxiliary_rank),
                tensorFormRankBlock(spec.left.index, slot.rank),
                spec.orthogonal_dimension,
                slot.rank,
                slot.output_rank,
                slot.auxiliary_rank,
                slot.chirality,
            ),
            else => return error.UnsupportedProjectorAdjointTerm,
        }
    }
}

fn appendCandidateWordAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorFormProjectionSpec, word: ProjectorCandidateWord) !void {
    var slot_index: u8 = 0;
    while (slot_index < word.count) : (slot_index += 1) {
        const slot = word.slots[slot_index];
        switch (slot.kind) {
            .gamma_insert => try atoms.append(allocator, .{ .gamma_form = .{
                .operator_id = spec.operator_id,
                .spinor_left = tensorSpinorSpinorIndex(spec.left),
                .spinor_right = spec.right,
                .form = slot.output_block,
                .orthogonal_dimension = spec.orthogonal_dimension,
                .rank = slot.rank,
                .chirality = spec.chirality,
            } }),
            .gamma_rank_split => try appendGammaRankSplitAtoms(
                allocator,
                atoms,
                spec.operator_id,
                tensorSpinorSpinorIndex(spec.left),
                spec.right,
                tensorFormRankBlock(spec.left, slot.rank),
                tensorFormRankBlock(spec.output, slot.output_rank),
                tensorFormRankBlock(spec.output, slot.auxiliary_rank),
                spec.orthogonal_dimension,
                slot.rank,
                slot.output_rank,
                slot.auxiliary_rank,
                spec.chirality,
            ),
            .form_delta => try atoms.append(allocator, .{ .generalized_delta = .{
                .upper = if (slot.input_block == 0) tensorFormCarriedBlock(spec.left) else slot.input_block,
                .lower = if (slot.output_block == 0) tensorFormCarriedBlock(spec.output) else slot.output_block,
            } }),
            .hodge_project => try appendExteriorGammaActionAtom(allocator, atoms, spec.operator_id, spec.left, spec.right, spec.output, slot),
            else => return error.UnsupportedTensorFormProjectionTerm,
        }
    }
}

fn appendCandidateWordAdjointAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: TensorFormProjectionSpec, word: ProjectorCandidateWord) !void {
    var remaining = word.count;
    while (remaining != 0) {
        remaining -= 1;
        const slot = word.slots[remaining];
        switch (slot.kind) {
            .form_delta => try atoms.append(allocator, .{ .generalized_delta = .{
                .upper = if (slot.output_block == 0) tensorFormCarriedBlock(spec.output) else slot.output_block,
                .lower = if (slot.input_block == 0) tensorFormCarriedBlock(spec.left) else slot.input_block,
            } }),
            .gamma_insert => try atoms.append(allocator, .{ .gamma_action = .{
                .operator_id = spec.operator_id,
                .form = slot.output_block,
                .spinor_input = spec.right,
                .spinor_output = tensorSpinorSpinorIndex(spec.left),
                .orthogonal_dimension = spec.orthogonal_dimension,
                .rank = slot.rank,
                .chirality = spec.chirality,
            } }),
            .hodge_project => try appendExteriorGammaActionAtom(allocator, atoms, spec.operator_id, spec.output, spec.right, spec.left, slot),
            .gamma_rank_split => try appendGammaRankSplitAdjointAtoms(
                allocator,
                atoms,
                spec.operator_id,
                spec.right,
                tensorSpinorSpinorIndex(spec.left),
                tensorFormRankBlock(spec.output, slot.output_rank),
                tensorFormRankBlock(spec.output, slot.auxiliary_rank),
                tensorFormRankBlock(spec.left, slot.rank),
                spec.orthogonal_dimension,
                slot.rank,
                slot.output_rank,
                slot.auxiliary_rank,
                spec.chirality,
            ),
            else => return error.UnsupportedProjectorAdjointTerm,
        }
    }
}

fn rationalToRenderingId(value: Rational) !rendering.RationalId {
    if (value.numerator < std.math.minInt(i32) or value.numerator > std.math.maxInt(i32)) return error.GramIntegerOverflow;
    if (value.denominator <= 0 or value.denominator > std.math.maxInt(u32)) return error.GramIntegerOverflow;
    return rendering.rationalFromSmall(@intCast(value.numerator), @intCast(value.denominator));
}

/// tensorFormProjectionTransition classifies tensor-form projector profiles.
pub fn tensorFormProjectionTransition(spec: TensorFormProjectionSpec) TensorFormProjectionTransition {
    if (spec.output_duality != .none and isMiddleDualProjection(spec)) return .middle_dual;
    if (spec.output_duality == .none and inferTerminalGammaRank(spec.input_form_profile, spec.output_form_profile) != null) return .gamma_delta;
    if (spec.output_duality == .none and isRankSplitProjection(spec)) return .rank_split;
    return .unsupported;
}

/// tensorFormProjectionUsesGammaWedge reports one-term gamma-form lowerability.
pub fn tensorFormProjectionUsesGammaWedge(spec: TensorFormProjectionSpec) bool {
    return tensorFormProjectionTransition(spec) == .gamma_delta;
}

fn tensorSpinorProjectionTransition(spec: TensorSpinorProjectionSpec) TensorSpinorProjectionTransition {
    if (spec.input_form_profile == 0 and
        spec.input_form_count == 0 and
        spec.form_rank == 0 and
        spec.form_count == 0 and
        spec.form_mask == 0 and
        spec.form_profile == 0 and
        spec.tower_power != 0 and
        spec.duality == .none)
    {
        return .spinor_tower_contract;
    }
    return .unsupported;
}

/// vectorSpinorTracelessTermCount returns the streamed term count.
pub fn vectorSpinorTracelessTermCount(spec: VectorSpinorTracelessSpec) u16 {
    const program = compileVectorSpinorTracelessProgram(spec) catch return 0;
    return projectorProgramTermCount(program);
}

/// appendVectorSpinorTracelessTerm emits one term of I - gamma-trace/N.
pub fn appendVectorSpinorTracelessTerm(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: VectorSpinorTracelessSpec, term_index: u16) !rendering.RationalId {
    const program = try compileVectorSpinorTracelessProgram(spec);
    const term = try projectorProgramTermAt(program, term_index);
    if (term.left_candidate != term.right_candidate) return error.UnsupportedVectorSpinorTracelessTerm;
    try appendVectorSpinorCandidateWordAtoms(allocator, atoms, spec, program.candidates[term.left_candidate]);
    return rationalToRenderingId(term.coefficient);
}

fn compileVectorSpinorTracelessProgram(spec: VectorSpinorTracelessSpec) !ProjectorProgram {
    return compileProjectorProgramForChannel(.{ .vector_spinor_traceless = spec }, orthogonalVectorSpinorTracelessBackend());
}

fn enumerateVectorSpinorTracelessCandidateWords(spec: VectorSpinorTracelessSpec) !ProjectorCandidateBuffer {
    var buffer: ProjectorCandidateBuffer = .{};
    var identity: ProjectorCandidateWord = .{};
    try identity.append(.{
        .kind = .vector_spinor_identity,
        .input_block = spec.vector,
        .output_block = spec.spinor,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = spec.chirality,
    });
    try buffer.append(identity);

    var trace: ProjectorCandidateWord = .{};
    try trace.append(.{
        .kind = .gamma_trace,
        .input_block = spec.vector,
        .output_block = spec.spinor,
        .orthogonal_dimension = spec.orthogonal_dimension,
        .chirality = spec.chirality,
    });
    try buffer.append(trace);
    return buffer;
}

fn vectorSpinorTracelessInnerProduct(_: ?*const anyopaque, left: ProjectorCandidateWord, right: ProjectorCandidateWord) !Rational {
    const left_slot = singlePrimitive(left) orelse return Rational.zero();
    const right_slot = singlePrimitive(right) orelse return Rational.zero();
    if (left_slot.input_block != right_slot.input_block or
        left_slot.output_block != right_slot.output_block or
        left_slot.orthogonal_dimension != right_slot.orthogonal_dimension or
        left_slot.chirality != right_slot.chirality)
    {
        return Rational.zero();
    }
    if (left_slot.kind != right_slot.kind) return Rational.zero();
    return switch (left_slot.kind) {
        .vector_spinor_identity => Rational.one(),
        .gamma_trace => Rational.init(-@as(i64, @intCast(left_slot.orthogonal_dimension)), 1),
        else => error.UnsupportedContraction,
    };
}

fn orthogonalVectorSpinorTracelessBackend() ProjectorBackend {
    return .{
        .enumerate_candidates = orthogonalVectorSpinorTracelessEnumerateCandidates,
        .inner_product = orthogonalVectorSpinorTracelessInnerProduct,
    };
}

fn orthogonalVectorSpinorTracelessEnumerateCandidates(_: ?*const anyopaque, channel: ProjectorChannel, candidates: *ProjectorCandidateBuffer) !void {
    const spec = switch (channel) {
        .vector_spinor_traceless => |spec| spec,
        else => return error.UnsupportedProjectorProgram,
    };
    if (spec.orthogonal_dimension == 0) return error.InvalidVectorSpinorTracelessDimension;
    candidates.* = try enumerateVectorSpinorTracelessCandidateWords(spec);
}

fn orthogonalVectorSpinorTracelessInnerProduct(_: ?*const anyopaque, channel: ProjectorChannel, left: ProjectorCandidateWord, right: ProjectorCandidateWord) !Rational {
    switch (channel) {
        .vector_spinor_traceless => {},
        else => return error.UnsupportedProjectorProgram,
    }
    return vectorSpinorTracelessInnerProduct(null, left, right);
}

fn singlePrimitive(word: ProjectorCandidateWord) ?ProjectorPrimitive {
    return if (word.count == 1) word.slots[0] else null;
}

fn appendVectorSpinorCandidateWordAtoms(allocator: std.mem.Allocator, atoms: *std.ArrayList(rendering.SymbolicAtom), spec: VectorSpinorTracelessSpec, word: ProjectorCandidateWord) !void {
    const slot = singlePrimitive(word) orelse return error.UnsupportedVectorSpinorTracelessTerm;
    switch (slot.kind) {
        .vector_spinor_identity => try atoms.append(allocator, .{ .vector_spinor_identity = .{
            .operator_id = spec.operator_id,
            .vector = spec.vector,
            .spinor = spec.spinor,
            .orthogonal_dimension = spec.orthogonal_dimension,
            .chirality = spec.chirality,
        } }),
        .gamma_trace => try atoms.append(allocator, .{ .gamma_trace = .{
            .operator_id = spec.operator_id,
            .vector = spec.vector,
            .spinor = spec.spinor,
            .orthogonal_dimension = spec.orthogonal_dimension,
            .chirality = spec.chirality,
        } }),
        else => return error.UnsupportedVectorSpinorTracelessTerm,
    }
}

/// inferTerminalGammaRank finds the gamma rank from input/output form profiles.
pub fn inferTerminalGammaRank(input: u128, output: u128) ?u8 {
    const transform = classifyProfileTransform(input, output);
    return switch (transform.kind) {
        .add_rank => transform.rank,
        .shift_all_up, .move_rank_up => transform.target_rank - transform.source_rank,
        else => null,
    };
}

fn classifyProfileTransform(input: u128, output: u128) ProfileTransform {
    if (input == output) return .{ .kind = .preserve };
    if (profileAddedRank(input, output)) |rank| return .{
        .kind = .add_rank,
        .rank = rank,
    };
    if (inferRankSplitProfile(input, output)) |split| return .{
        .kind = .split_rank,
        .source_rank = split.source_rank,
        .lower_rank = split.lower_rank,
        .upper_rank = split.upper_rank,
        .carried_profile = split.carried_profile,
    };
    if (profileTotalPower(output) == profileTotalPower(input)) {
        var shift: u8 = 1;
        while (shift < 32) : (shift += 1) {
            if (profileShiftedBy(input, output, shift)) return .{
                .kind = .shift_all_up,
                .source_rank = 1,
                .target_rank = shift + 1,
            };
        }
        if (profileMovedRank(input, output)) |move| return .{
            .kind = .move_rank_up,
            .source_rank = move.source_rank,
            .target_rank = move.target_rank,
        };
    }
    if (profileRemovedRank(input, output)) |rank| return .{
        .kind = .remove_rank,
        .rank = rank,
    };
    return .{ .kind = .unsupported };
}

fn profileTotalPower(profile: u128) u16 {
    var total: u16 = 0;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        total += profileSlot(profile, rank_index);
    }
    return total;
}

fn profileSingleIncrementRank(input: u128, output: u128) ?u8 {
    var found: ?u8 = null;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const in = profileSlot(input, rank_index);
        const out = profileSlot(output, rank_index);
        if (out == in) continue;
        if (out != in + 1 or found != null) return null;
        found = rank_index + 1;
    }
    return found;
}

fn profileAddedRank(input: u128, output: u128) ?u8 {
    if (profileTotalPower(output) != profileTotalPower(input) + 1) return null;
    var found: ?u8 = null;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const in = profileSlot(input, rank_index);
        const out = profileSlot(output, rank_index);
        if (out == in) continue;
        if (out != in + 1 or found != null) return null;
        found = rank_index + 1;
    }
    return found;
}

fn profileMask(profile: u128) u64 {
    var mask: u64 = 0;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        if (profileSlot(profile, rank_index) != 0) mask |= @as(u64, 1) << @intCast(rank_index);
    }
    return mask;
}

fn formProfileFromMask(mask: u64) u128 {
    var profile: u128 = 0;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        if ((mask & (@as(u64, 1) << @intCast(rank_index))) != 0) {
            profile |= @as(u128, 1) << @intCast(rank_index * 4);
        }
    }
    return profile;
}

fn profileShiftedBy(input: u128, output: u128, shift: u8) bool {
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const expected: u8 = if (rank_index >= shift) profileSlot(input, rank_index - shift) else 0;
        if (profileSlot(output, rank_index) != expected) return false;
    }
    return true;
}

fn profileUniformShiftDown(input: u128, output: u128) ?u8 {
    var shift: u8 = 1;
    while (shift < 32) : (shift += 1) {
        if (profileShiftedBy(output, input, shift)) return shift;
    }
    return null;
}

fn highestShiftedSourceRank(input: u128, output: u128, shift: u8) ?u8 {
    var rank_index: u8 = 32;
    while (rank_index > 0) {
        rank_index -= 1;
        const source_rank = rank_index + 1;
        if (source_rank <= shift) continue;
        if (profileSlot(input, rank_index) <= profileSlot(output, rank_index)) continue;
        const target_rank = source_rank - shift;
        if (profileSlot(input, target_rank - 1) >= profileSlot(output, target_rank - 1)) continue;
        return source_rank;
    }
    return null;
}

fn nextUniformShiftDownMove(input: u128, output: u128, shift: u8) ?ProfileRankMove {
    var rank_index: u8 = 32;
    while (rank_index > 0) {
        rank_index -= 1;
        const source_rank = rank_index + 1;
        if (source_rank <= shift) continue;
        if (profileSlot(input, rank_index) <= profileSlot(output, rank_index)) continue;
        const target_rank = source_rank - shift;
        if (profileSlot(input, target_rank - 1) >= profileSlot(output, target_rank - 1)) continue;
        return .{
            .source_rank = source_rank,
            .target_rank = target_rank,
        };
    }
    return null;
}

fn profileMovedRank(input: u128, output: u128) ?ProfileRankMove {
    var source: ?u8 = null;
    var target: ?u8 = null;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const in = profileSlot(input, rank_index);
        const out = profileSlot(output, rank_index);
        if (in == out) continue;
        if (in == out + 1 and source == null) {
            source = rank_index;
        } else if (out == in + 1 and target == null) {
            target = rank_index;
        } else {
            return null;
        }
    }
    const from = source orelse return null;
    const to = target orelse return null;
    if (to <= from) return null;
    return .{
        .source_rank = from + 1,
        .target_rank = to + 1,
    };
}

fn profileMovedAnyRank(input: u128, output: u128) ?ProfileRankMove {
    if (profileTotalPower(input) != profileTotalPower(output)) return null;
    var source: ?u8 = null;
    var target: ?u8 = null;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const in = profileSlot(input, rank_index);
        const out = profileSlot(output, rank_index);
        if (in == out) continue;
        if (in == out + 1 and source == null) {
            source = rank_index;
        } else if (out == in + 1 and target == null) {
            target = rank_index;
        } else {
            return null;
        }
    }
    const from = source orelse return null;
    const to = target orelse return null;
    if (from == to) return null;
    return .{
        .source_rank = from + 1,
        .target_rank = to + 1,
    };
}

fn profileRemovedRank(input: u128, output: u128) ?u8 {
    if (profileTotalPower(input) != profileTotalPower(output) + 1) return null;
    var found: ?u8 = null;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const in = profileSlot(input, rank_index);
        const out = profileSlot(output, rank_index);
        if (in == out) continue;
        if (in != out + 1 or found != null) return null;
        found = rank_index + 1;
    }
    return found;
}

fn profileIncrementedRank(profile: u128, rank: u8) u128 {
    return profile + (@as(u128, 1) << @intCast((rank - 1) * 4));
}

fn profileDecrementedRank(profile: u128, rank: u8) u128 {
    return profile - (@as(u128, 1) << @intCast((rank - 1) * 4));
}

fn profileIntersection(left: u128, right: u128) u128 {
    var out: u128 = 0;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const count = @min(profileSlot(left, rank_index), profileSlot(right, rank_index));
        out |= @as(u128, count) << @intCast(rank_index * 4);
    }
    return out;
}

fn profilePositiveDeficitPower(current: u128, target: u128) u16 {
    var total: u16 = 0;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const have = profileSlot(current, rank_index);
        const need = profileSlot(target, rank_index);
        if (need > have) total += need - have;
    }
    return total;
}

fn profileOnlyRank(profile: u128) ?u8 {
    var found: ?u8 = null;
    var rank_index: u8 = 0;
    while (rank_index < 32) : (rank_index += 1) {
        const count = profileSlot(profile, rank_index);
        if (count == 0) continue;
        if (count != 1 or found != null) return null;
        found = rank_index + 1;
    }
    return found;
}

fn isRankSplitProjection(spec: TensorFormProjectionSpec) bool {
    return classifyProfileTransform(spec.input_form_profile, spec.output_form_profile).kind == .split_rank or
        hasTerminalGammaRankSplitProjection(spec);
}

fn isMiddleDualProjection(spec: TensorFormProjectionSpec) bool {
    if (spec.output_form_profile != 0 or spec.output_form_count != 1) return false;
    return spec.output_form_rank != 0 and @as(u16, spec.output_form_rank) * 2 == spec.orthogonal_dimension;
}

fn hasTerminalGammaRankSplitProjection(spec: TensorFormProjectionSpec) bool {
    if (spec.output_duality != .none) return false;
    if (spec.orthogonal_dimension == 0 or spec.orthogonal_dimension > std.math.maxInt(u8)) return false;
    if (profileTotalPower(spec.output_form_profile) != profileTotalPower(spec.input_form_profile) + 1) return false;

    const dimension: u8 = @intCast(spec.orthogonal_dimension);
    var input_rank: u8 = 1;
    while (input_rank <= dimension) : (input_rank += 1) {
        if (profileSlot(spec.input_form_profile, input_rank - 1) == 0) continue;
        const removed = profileDecrementedRank(spec.input_form_profile, input_rank);
        var lower_rank: u8 = 1;
        while (lower_rank <= dimension) : (lower_rank += 1) {
            if (lower_rank == input_rank) continue;
            var auxiliary_rank: u8 = lower_rank;
            while (auxiliary_rank <= dimension) : (auxiliary_rank += 1) {
                if (auxiliary_rank == input_rank or auxiliary_rank == lower_rank) continue;
                const candidate = profileIncrementedRank(profileIncrementedRank(removed, lower_rank), auxiliary_rank);
                if (candidate != spec.output_form_profile) continue;
                if (!spinorBilinearChiralityValid(spec.chirality, spec.right_chirality, rankSplitBilinearParityRank(input_rank, lower_rank, auxiliary_rank))) continue;
                if (firstExteriorGammaAction(spec.orthogonal_dimension, input_rank, lower_rank, .none) != null) return true;
            }
        }
    }
    return false;
}

fn profileSingleSplitToNeighbors(input: u128, output: u128) bool {
    return classifyProfileTransform(input, output).kind == .split_rank;
}

fn inferRankSplitProfile(input: u128, output: u128) ?RankSplitProfile {
    if (profileTotalPower(output) != profileTotalPower(input) + 1) return null;
    var found: ?RankSplitProfile = null;
    var rank_index: u8 = 1;
    while (rank_index < 31) : (rank_index += 1) {
        if (profileSlot(input, rank_index) == 0) continue;
        const removed = input - (@as(u128, 1) << @intCast(rank_index * 4));
        const lower_index = rank_index - 1;
        var upper_index = lower_index + 1;
        while (upper_index < 32) : (upper_index += 1) {
            if (upper_index == rank_index) continue;
            var candidate = removed;
            candidate += @as(u128, 1) << @intCast(lower_index * 4);
            candidate += @as(u128, 1) << @intCast(upper_index * 4);
            if (candidate != output) continue;
            if (found != null) return null;
            found = .{
                .source_rank = rank_index + 1,
                .lower_rank = lower_index + 1,
                .upper_rank = upper_index + 1,
                .carried_profile = removed,
            };
        }
    }
    return found;
}

fn profileSlot(profile: u128, rank_index: u8) u8 {
    return @intCast((profile >> @intCast(rank_index * 4)) & 0xf);
}

fn tensorSpinorSpinorIndex(index: rendering.IndexRef) rendering.IndexRef {
    return 0x80000000 | index;
}

fn tensorFormInsertedBlock(index: rendering.IndexRef, rank: u8) rendering.IndexBlockId {
    return tensorFormRankBlock(index, rank);
}

fn tensorFormRankBlock(index: rendering.IndexRef, rank: u8) rendering.IndexBlockId {
    return 0x40000000 | (@as(u32, rank) << 24) | (index & 0x00ffffff);
}

fn tensorFormBlockRank(block: rendering.IndexBlockId) ?u8 {
    return if ((block & 0xf0000000) == 0x40000000) @intCast((block >> 24) & 0x3f) else null;
}

fn tensorFormCarriedBlock(index: rendering.IndexRef) rendering.IndexBlockId {
    return 0x60000000 | (index & 0x0fffffff);
}

fn dependentCandidateFixtureInnerProduct(_: ?*const anyopaque, _: ProjectorCandidateWord, _: ProjectorCandidateWord) !Rational {
    return Rational.one();
}

fn offDiagonalFixtureInnerProduct(_: ?*const anyopaque, left: ProjectorCandidateWord, right: ProjectorCandidateWord) !Rational {
    const left_slot = singlePrimitive(left) orelse return Rational.zero();
    const right_slot = singlePrimitive(right) orelse return Rational.zero();
    if (left_slot.kind != .form_delta or right_slot.kind != .form_delta) return Rational.zero();
    return if (left_slot.rank == right_slot.rank) Rational.init(2, 1) else Rational.one();
}

fn gammaRankSplitOffDiagonalFixtureInnerProduct(_: ?*const anyopaque, left: ProjectorCandidateWord, right: ProjectorCandidateWord) !Rational {
    const left_slot = singlePrimitive(left) orelse return Rational.zero();
    const right_slot = singlePrimitive(right) orelse return Rational.zero();
    if (left_slot.kind != .gamma_rank_split or right_slot.kind != .gamma_rank_split) return Rational.zero();
    return if (left_slot.rank == right_slot.rank) Rational.init(2, 1) else Rational.one();
}

fn pivotCapFixtureInnerProduct(_: ?*const anyopaque, left: ProjectorCandidateWord, right: ProjectorCandidateWord) !Rational {
    const left_slot = singlePrimitive(left) orelse return Rational.zero();
    const right_slot = singlePrimitive(right) orelse return Rational.zero();
    return if (left_slot.input_block == right_slot.input_block) Rational.one() else Rational.zero();
}

fn structuralFixtureInnerProduct(_: ?*const anyopaque, left: ProjectorCandidateWord, right: ProjectorCandidateWord) !Rational {
    return structuralCandidateInnerProduct(left, right);
}

fn backendFixtureEnumerateCandidates(_: ?*const anyopaque, _: ProjectorChannel, candidates: *ProjectorCandidateBuffer) !void {
    var word: ProjectorCandidateWord = .{};
    try word.append(.{
        .kind = .form_delta,
        .input_block = 1,
        .output_block = 2,
        .rank = 7,
    });
    try candidates.append(word);
}

fn backendFixtureInnerProduct(_: ?*const anyopaque, _: ProjectorChannel, left: ProjectorCandidateWord, right: ProjectorCandidateWord) !Rational {
    const left_slot = singlePrimitive(left) orelse return Rational.zero();
    const right_slot = singlePrimitive(right) orelse return Rational.zero();
    if (!projectorPrimitiveEql(left_slot, right_slot)) return Rational.zero();
    return Rational.init(2, 1);
}

fn tensorOnlyTestEndpoint(side: TensorEndpointSide, slot_count: u8) TensorOnlyEndpoint {
    var layout: TensorOnlyEndpointLayout = .{ .slot_count = slot_count };
    var slot: u8 = 0;
    while (slot < slot_count) : (slot += 1) {
        layout.slots[slot] = .{ .block = @intFromEnum(side), .slot = slot };
    }
    return .{
        .side = side,
        .block = @intFromEnum(side),
        .kind = if (slot_count == 0) .scalar else .vector_young,
        .slot_count = slot_count,
        .layout = layout,
        .row_count = if (slot_count == 0) 0 else 1,
        .rows = blk: {
            var rows = [_]u8{0} ** max_young_rows;
            rows[0] = slot_count;
            break :blk rows;
        },
        .column_count = slot_count,
        .column_heights = blk: {
            var columns = [_]u8{0} ** max_young_rows;
            var column: u8 = 0;
            while (column < slot_count and column < max_young_rows) : (column += 1) {
                columns[column] = 1;
            }
            break :blk columns;
        },
    };
}

fn tensorOnlyTestChannel(left_slots: u8, right_slots: u8, output_slots: u8) TensorOnlyChannel {
    return .{
        .operator_id = 1,
        .dimension = 10,
        .left = tensorOnlyTestEndpoint(.left, left_slots),
        .right = tensorOnlyTestEndpoint(.right, right_slots),
        .output = tensorOnlyTestEndpoint(.output, output_slots),
        .input_slot_count = left_slots + right_slots,
        .output_slot_count = output_slots,
    };
}

fn tensorOnlyHookTestEndpoint(side: TensorEndpointSide) TensorOnlyEndpoint {
    var endpoint = tensorOnlyTestEndpoint(side, 3);
    endpoint.row_count = 2;
    endpoint.rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 };
    endpoint.column_count = 2;
    endpoint.column_heights = .{ 2, 1, 0, 0, 0, 0, 0, 0 };
    return endpoint;
}

fn expectTensorEndpointActionBuildBuffersEql(left: TensorEndpointActionBuildBuffer, right: TensorEndpointActionBuildBuffer) !void {
    const testing = std.testing;
    try testing.expectEqual(left.word_count, right.word_count);
    var left_index: u8 = 0;
    while (left_index < left.word_count) : (left_index += 1) {
        var found = false;
        var right_index: u8 = 0;
        while (right_index < right.word_count) : (right_index += 1) {
            if (!brauerWordEql(left.words[left_index].word, right.words[right_index].word)) continue;
            if (!tensorEndpointActionWordHodgeEql(left.words[left_index], right.words[right_index])) continue;
            found = true;
            break;
        }
        try testing.expect(found);
    }
}

fn expectStructuralTensorOnlyPrimitiveRoute(spec: StructuralProjectorSpec, require_hodge: bool) !void {
    const testing = std.testing;
    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();

    const term_count = try cache.termCount(spec);
    try testing.expect(term_count != 0);
    try testing.expectEqual(@as(usize, 1), cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), cache.vector_entries.items.len);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var saw_hodge = false;
    var term_index: u16 = 0;
    while (term_index < term_count) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try cache.appendTerm(&atoms, spec, term_index);
        try testing.expect(atoms.items.len != 0);
        for (atoms.items) |atom| switch (atom) {
            .vector_slot_delta, .vector_slot_metric => {},
            .hodge_star => saw_hodge = true,
            else => return error.ExpectedTensorOnlyPrimitiveAtom,
        };
    }
    if (require_hodge) try testing.expect(saw_hodge);
}

test "projector constructor enumerates raw tensor-only Brauer scalar pairing diagrams" {
    const testing = std.testing;
    const channel = tensorOnlyTestChannel(1, 1, 0);
    var diagrams: TensorBrauerDiagramBuffer = .{};
    try enumerateRawBrauerDiagrams(channel, &diagrams);

    try testing.expectEqual(@as(u8, 1), diagrams.count);
    try testing.expectEqual(@as(u8, 1), diagrams.diagrams[0].edge_count);
    try testing.expectEqual(BrauerEdgeKind.input_trace, diagrams.diagrams[0].edges[0].kind);
    try testing.expectEqual(@as(u8, 0), diagrams.diagrams[0].edges[0].input_a);
    try testing.expectEqual(@as(u8, 1), diagrams.diagrams[0].edges[0].input_b);
}

test "projector constructor enumerates all equal-rank raw tensor-only Brauer diagrams" {
    const testing = std.testing;
    const channel = tensorOnlyTestChannel(1, 1, 2);
    var diagrams: TensorBrauerDiagramBuffer = .{};
    try enumerateRawBrauerDiagrams(channel, &diagrams);

    try testing.expectEqual(@as(u8, 3), diagrams.count);
    var delta_pair_count: u8 = 0;
    var metric_pair_count: u8 = 0;
    var diagram_index: u8 = 0;
    while (diagram_index < diagrams.count) : (diagram_index += 1) {
        const diagram = diagrams.diagrams[diagram_index];
        try testing.expectEqual(@as(u8, 2), diagram.edge_count);
        var delta_count: u8 = 0;
        var input_metric_count: u8 = 0;
        var output_metric_count: u8 = 0;
        var edge_index: u8 = 0;
        while (edge_index < diagram.edge_count) : (edge_index += 1) {
            switch (diagram.edges[edge_index].kind) {
                .delta => delta_count += 1,
                .input_trace => input_metric_count += 1,
                .output_metric => output_metric_count += 1,
            }
        }
        if (delta_count == 2) delta_pair_count += 1;
        if (input_metric_count == 1 and output_metric_count == 1) metric_pair_count += 1;
    }
    try testing.expectEqual(@as(u8, 2), delta_pair_count);
    try testing.expectEqual(@as(u8, 1), metric_pair_count);
}

test "projector constructor raw tensor-only Brauer diagrams depend only on slot counts" {
    const testing = std.testing;
    const vector_channel = tensorOnlyTestChannel(1, 1, 2);
    var mixed_channel = vector_channel;
    mixed_channel.left.kind = .exterior_form;
    mixed_channel.left.row_count = 2;
    mixed_channel.left.rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 };
    mixed_channel.left.form_profile = @as(u128, 1) << 4;
    mixed_channel.left.form_rank = 2;
    mixed_channel.right.kind = .mixed_tensor_form;
    mixed_channel.right.form_profile = @as(u128, 1) << 0;
    mixed_channel.output.kind = .mixed_tensor_form;
    mixed_channel.output.row_count = 2;
    mixed_channel.output.rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 };
    mixed_channel.output.form_profile = @as(u128, 1) << 4;

    var vector_diagrams: TensorBrauerDiagramBuffer = .{};
    var mixed_diagrams: TensorBrauerDiagramBuffer = .{};
    try enumerateRawBrauerDiagrams(vector_channel, &vector_diagrams);
    try enumerateRawBrauerDiagrams(mixed_channel, &mixed_diagrams);

    try testing.expectEqual(vector_diagrams.count, mixed_diagrams.count);
    var diagram_index: u8 = 0;
    while (diagram_index < vector_diagrams.count) : (diagram_index += 1) {
        try testing.expect(brauerWordEql(vector_diagrams.diagrams[diagram_index], mixed_diagrams.diagrams[diagram_index]));
    }
}

test "projector constructor enumerates two-form scalar raw metric pairings" {
    const testing = std.testing;
    const channel = tensorOnlyTestChannel(2, 2, 0);
    var diagrams: TensorBrauerDiagramBuffer = .{};
    try enumerateRawBrauerDiagrams(channel, &diagrams);

    try testing.expectEqual(@as(u8, 3), diagrams.count);
    var diagram_index: u8 = 0;
    while (diagram_index < diagrams.count) : (diagram_index += 1) {
        const diagram = diagrams.diagrams[diagram_index];
        try testing.expectEqual(@as(u8, 2), diagram.edge_count);
        var edge_index: u8 = 0;
        while (edge_index < diagram.edge_count) : (edge_index += 1) {
            try testing.expectEqual(BrauerEdgeKind.input_trace, diagram.edges[edge_index].kind);
        }
    }
}

test "projector constructor prunes raw diagrams killed by endpoint trace-free projectors" {
    const testing = std.testing;

    const scalar_pairing = tensorOnlyTestChannel(2, 2, 0);
    var scalar_diagrams: TensorBrauerDiagramBuffer = .{};
    try enumerateRawBrauerDiagrams(scalar_pairing, &scalar_diagrams);
    try pruneTensorOnlyTraceKilledRawDiagrams(scalar_pairing, &scalar_diagrams);
    try testing.expectEqual(@as(u8, 2), scalar_diagrams.count);
    var diagram_index: u8 = 0;
    while (diagram_index < scalar_diagrams.count) : (diagram_index += 1) {
        const diagram = scalar_diagrams.diagrams[diagram_index];
        var edge_index: u8 = 0;
        while (edge_index < diagram.edge_count) : (edge_index += 1) {
            const edge = diagram.edges[edge_index];
            try testing.expectEqual(BrauerEdgeKind.input_trace, edge.kind);
            try testing.expect(edge.input_a < scalar_pairing.left.slot_count);
            try testing.expect(edge.input_b >= scalar_pairing.left.slot_count);
        }
    }

    const young_output = tensorOnlyTestChannel(2, 2, 4);
    var young_diagrams: TensorBrauerDiagramBuffer = .{};
    try enumerateRawBrauerDiagrams(young_output, &young_diagrams);
    try pruneTensorOnlyTraceKilledRawDiagrams(young_output, &young_diagrams);
    try testing.expectEqual(@as(u8, 24), young_diagrams.count);
    diagram_index = 0;
    while (diagram_index < young_diagrams.count) : (diagram_index += 1) {
        const diagram = young_diagrams.diagrams[diagram_index];
        var edge_index: u8 = 0;
        while (edge_index < diagram.edge_count) : (edge_index += 1) {
            try testing.expectEqual(BrauerEdgeKind.delta, diagram.edges[edge_index].kind);
        }
    }
}

test "projector constructor rejects odd raw tensor-only Brauer boundaries" {
    const testing = std.testing;
    const channel = tensorOnlyTestChannel(1, 0, 0);
    var diagrams: TensorBrauerDiagramBuffer = .{};
    try testing.expectError(error.UnsupportedStructuralProjectorTerm, enumerateRawBrauerDiagrams(channel, &diagrams));
}

test "projector constructor reports raw tensor-only Brauer diagram cap" {
    const testing = std.testing;
    const channel = tensorOnlyTestChannel(5, 5, 0);
    var diagrams: TensorBrauerDiagramBuffer = .{};
    try testing.expectError(error.UnsupportedTensorBrauerCandidateCap, enumerateRawBrauerDiagrams(channel, &diagrams));
}

test "projector constructor budgets raw tensor-only diagrams before compile enumeration" {
    const testing = std.testing;
    try testing.expectError(error.ProjectorProgramTooLarge, compileGeneralTensorOnlyBrauerProgram(tensorOnlyTestChannel(5, 5, 0)));
}

test "projector constructor builds factorized tensor-only raw candidate words" {
    const testing = std.testing;
    const program = try compileTensorOnlyBrauerProgram(tensorOnlyTestChannel(1, 1, 2));

    try testing.expectEqual(@as(u8, 2), program.raw_diagram_count);
    try testing.expectEqual(program.raw_diagram_count, program.candidate_count);
    try testing.expect(tensorOnlyProgramLeftProjector(&program).is_identity);
    try testing.expect(tensorOnlyProgramRightProjector(&program).is_identity);
    try testing.expect(!tensorOnlyProgramOutputProjector(&program).is_identity);
    try testing.expectEqual(@as(u8, 2), tensorOnlyProgramOutputProjector(&program).operator_count);
    try testing.expectEqual(TensorEndpointOperatorKind.young_row_symmetrizer, tensorOnlyProgramOutputProjector(&program).operators[0].kind);
    try testing.expectEqual(@as(u8, 2), tensorOnlyProgramOutputProjector(&program).operators[0].slot_count);
    try testing.expectEqual(TensorEndpointOperatorKind.trace_removal_projector, tensorOnlyProgramOutputProjector(&program).operators[1].kind);
    try testing.expectEqual(@as(u8, 1), tensorOnlyProgramOutputProjector(&program).operators[1].trace_generator_count);
    try testing.expectEqual(@as(u8, 2), tensorOnlyProgramOutputProjector(&program).operators[1].trace_basis_count);
    try testing.expectEqual(@as(u8, 1), tensorOnlyProgramOutputProjector(&program).operators[1].trace_branch_count);
    try testing.expectEqual(@as(u8, 1), tensorOnlyProgramOutputProjector(&program).trace_branch_count);
    try testing.expectEqual(@as(u8, 1), tensorOnlyProgramOutputProjector(&program).trace_branches[0].trace_count);
    try testing.expectEqual(@as(u8, 0), tensorOnlyProgramOutputProjector(&program).trace_branches[0].trace_slot_a[0]);
    try testing.expectEqual(@as(u8, 1), tensorOnlyProgramOutputProjector(&program).trace_branches[0].trace_slot_b[0]);
    try testing.expectEqual(@as(u8, 0), tensorOnlyProgramOutputProjector(&program).trace_free.basis_count);

    var candidate_index: u8 = 0;
    while (candidate_index < program.candidate_count) : (candidate_index += 1) {
        const word = program.candidates[candidate_index];
        try testing.expectEqual(@as(u8, 2), word.factor_count);
        try testing.expectEqual(TensorOnlyFactorKind.raw_brauer_diagram, word.factors[0].kind);
        try testing.expectEqual(candidate_index, word.factors[0].candidate_index);
        try testing.expectEqual(TensorOnlyFactorKind.output_projector, word.factors[1].kind);
    }
}

test "projector constructor factorizes multi-trace symmetric endpoint actions" {
    const testing = std.testing;
    const endpoint = tensorOnlyTestEndpoint(.output, 3);
    const shape = try tensorOnlyEndpointShape(endpoint);
    var compact = try endpointProjector(endpoint, 10);
    defer compact.deinit();

    try testing.expect(!compact.is_identity);
    try testing.expectEqual(@as(u8, 2), compact.operator_count);
    try testing.expectEqual(TensorEndpointOperatorKind.young_row_symmetrizer, compact.operators[0].kind);
    try testing.expectEqual(TensorEndpointOperatorKind.trace_removal_projector, compact.operators[1].kind);
    try testing.expect(compact.operators[1].trace_generator_count > 1);
    try testing.expect(compact.operators[1].trace_branch_count > 1);
    try testing.expectEqual(compact.operators[1].trace_branch_count, compact.trace_branch_count);
    try testing.expectEqual(@as(u8, 0), compact.trace_free.basis_count);

    var branch_index: u8 = 0;
    while (branch_index < compact.trace_branch_count) : (branch_index += 1) {
        try testing.expect(compact.trace_branches[branch_index].trace_count != 0);
    }

    var young_candidates: BrauerCandidateBuffer = .{};
    try appendVectorYoungPermutationCandidates(shape, endpoint.slot_count, &young_candidates);
    try uniqueBrauerWords(&young_candidates);
    const trace_free = try traceFreeBrauerProjectorBasisForShape(shape, 10, young_candidates.candidates[0]);
    var expanded = EndpointProjector{
        .is_identity = false,
        .diagnostic_trace_free_basis = true,
        .trace_free = trace_free,
    };
    expanded.operators[0] = try tensorEndpointYoungTraceFreeFactor(shape);
    expanded.operators[0].trace_basis_count = trace_free.basis_count;
    expanded.operator_count = 1;
    defer expanded.deinit();

    var input: TensorEndpointActionBuildBuffer = .{};
    try appendTensorEndpointActionWord(&input, .{ .word = try identityBrauerWord(endpoint.slot_count) });
    const channel = tensorOnlyTestChannel(3, 0, 3);
    const compact_action = try applyTensorEndpointProjectorAction(channel, .output, &compact, input);
    const expanded_action = try applyTensorEndpointProjectorAction(channel, .output, &expanded, input);
    try expectTensorEndpointActionBuildBuffersEql(compact_action, expanded_action);
}

test "projector constructor factorizes mixed Young endpoint normalization" {
    const testing = std.testing;
    const endpoint = tensorOnlyHookTestEndpoint(.output);
    const shape = try tensorOnlyEndpointShape(endpoint);

    var compact = try endpointProjector(endpoint, 10);
    defer compact.deinit();

    try testing.expect(!compact.is_identity);
    try testing.expectEqual(TensorEndpointOperatorKind.young_row_symmetrizer, compact.operators[0].kind);
    try testing.expectEqual(TensorEndpointOperatorKind.young_column_antisymmetrizer, compact.operators[1].kind);
    try testing.expectEqual(TensorEndpointOperatorKind.scalar_multiplier, compact.operators[2].kind);
    try testing.expect(rationalValueEql(compact.operators[2].scalar_coefficient, try Rational.init(4, 3)));
    try testing.expectEqual(TensorEndpointOperatorKind.trace_removal_projector, compact.operators[3].kind);
    try testing.expectEqual(@as(u8, 0), compact.trace_free.basis_count);

    var young_candidates: BrauerCandidateBuffer = .{};
    try appendVectorYoungPermutationCandidates(shape, endpoint.slot_count, &young_candidates);
    try uniqueBrauerWords(&young_candidates);
    const trace_free = try traceFreeBrauerProjectorBasisForShape(shape, 10, young_candidates.candidates[0]);
    var expanded = EndpointProjector{
        .is_identity = false,
        .diagnostic_trace_free_basis = true,
        .trace_free = trace_free,
    };
    expanded.operators[0] = try tensorEndpointYoungTraceFreeFactor(shape);
    expanded.operators[0].trace_basis_count = trace_free.basis_count;
    expanded.operator_count = 1;
    defer expanded.deinit();

    var input: TensorEndpointActionBuildBuffer = .{};
    try appendTensorEndpointActionWord(&input, .{ .word = try identityBrauerWord(endpoint.slot_count) });
    const channel = tensorOnlyTestChannel(3, 0, 3);
    const compact_action = try applyTensorEndpointProjectorAction(channel, .output, &compact, input);
    const expanded_action = try applyTensorEndpointProjectorAction(channel, .output, &expanded, input);
    try expectTensorEndpointActionBuildBuffersEql(compact_action, expanded_action);
}

test "projector constructor fences expanded trace-free endpoint basis to diagnostics" {
    const testing = std.testing;
    var projector = EndpointProjector{
        .is_identity = false,
        .operator_count = 1,
    };
    projector.operators[0] = .{ .kind = .young_trace_free_projector };

    var input: TensorEndpointActionBuildBuffer = .{};
    try appendTensorEndpointActionWord(&input, .{ .word = try identityBrauerWord(2) });

    try testing.expectError(
        error.UnsupportedStructuralProjectorTerm,
        applyTensorEndpointProjectorAction(tensorOnlyTestChannel(2, 0, 2), .output, &projector, input),
    );
}

test "projector constructor compiles mixed Young tensor-only channel through compact endpoints" {
    const testing = std.testing;
    const channel: TensorOnlyChannel = .{
        .operator_id = 91,
        .dimension = 10,
        .left = tensorOnlyHookTestEndpoint(.left),
        .right = tensorOnlyTestEndpoint(.right, 0),
        .output = tensorOnlyHookTestEndpoint(.output),
        .input_slot_count = 3,
        .output_slot_count = 3,
    };
    var program = try compileGeneralTensorOnlyBrauerProgram(channel);
    defer program.deinit();

    try testing.expect(program.raw_diagram_count != 0);
    try testing.expect(program.candidate_count != 0);
    try testing.expect(program.pivot_count != 0);
    try testing.expect(program.term_count != 0);

    const left_projector = tensorOnlyProgramLeftProjector(&program);
    const output_projector = tensorOnlyProgramOutputProjector(&program);
    try testing.expectEqual(@as(u8, 0), left_projector.trace_free.basis_count);
    try testing.expectEqual(@as(u8, 0), output_projector.trace_free.basis_count);
    try testing.expectEqual(TensorEndpointOperatorKind.scalar_multiplier, left_projector.operators[2].kind);
    try testing.expectEqual(TensorEndpointOperatorKind.scalar_multiplier, output_projector.operators[2].kind);
}

test "projector constructor omits identity endpoint factors in tensor-only programs" {
    const testing = std.testing;
    const program = try compileTensorOnlyBrauerProgram(tensorOnlyTestChannel(1, 1, 0));

    try testing.expectEqual(@as(u8, 2), program.projector_count);
    try testing.expectEqual(@as(u8, 1), program.candidate_count);
    try testing.expectEqual(program.left_projector_index, program.right_projector_index);
    try testing.expect(program.left_projector_index != program.output_projector_index);
    try testing.expect(tensorOnlyProgramLeftProjector(&program).is_identity);
    try testing.expect(tensorOnlyProgramRightProjector(&program).is_identity);
    try testing.expect(tensorOnlyProgramOutputProjector(&program).is_identity);
    try testing.expectEqual(@as(u8, 1), program.candidates[0].factor_count);
    try testing.expectEqual(TensorOnlyFactorKind.raw_brauer_diagram, program.candidates[0].factors[0].kind);
}

test "projector constructor budgets endpoint projector factors before trace expansion" {
    const testing = std.testing;
    var endpoint = tensorOnlyTestEndpoint(.output, 8);
    endpoint.row_count = 2;
    endpoint.rows = .{ 4, 4, 0, 0, 0, 0, 0, 0 };
    endpoint.column_count = 4;
    endpoint.column_heights = .{ 2, 2, 2, 2, 0, 0, 0, 0 };

    const shape = try tensorOnlyEndpointShape(endpoint);
    const factor = try tensorEndpointYoungTraceFreeFactor(shape);
    try testing.expect(factor.young_word_upper_bound > max_young_permutation_terms);
    const channel = TensorOnlyChannel{
        .operator_id = 1,
        .dimension = 10,
        .left = endpoint,
        .right = tensorOnlyTestEndpoint(.right, 0),
        .output = tensorOnlyTestEndpoint(.output, 0),
        .input_slot_count = endpoint.slot_count,
        .output_slot_count = 0,
    };
    try testing.expectError(error.ProjectorProgramTooLarge, budgetTensorOnlyEndpointProjectorsBeforeConstruction(channel));
    try testing.expectError(error.ProjectorProgramTooLarge, endpointProjector(endpoint, 10));
}

test "projector constructor budgets endpoint action words before buffers" {
    const testing = std.testing;
    var program: TensorOnlyProgram = .{
        .channel = tensorOnlyTestChannel(1, 1, 0),
        .raw_diagram_count = 1,
        .projector_count = 1,
    };
    program.left_projector_index = 0;
    program.right_projector_index = 0;
    program.output_projector_index = 0;
    program.projectors[0] = .{
        .is_identity = false,
        .operator_count = 1,
    };
    program.projectors[0].operators[0] = .{
        .kind = .trace_removal_projector,
        .trace_branch_count = max_tensor_endpoint_action_words,
    };

    try testing.expectError(error.ProjectorProgramTooLarge, budgetTensorOnlyEndpointActionsBeforeConstruction(&program));
}

test "projector constructor caches tensor-only endpoint actions by raw side" {
    const testing = std.testing;
    const program = try compileTensorOnlyBrauerProgram(tensorOnlyTestChannel(1, 1, 2));

    try testing.expect(program.endpoint_action_count != 0);
    try testing.expect(program.endpoint_action_count <= @as(u16, program.raw_diagram_count) * 3);
    var action_index: u16 = 0;
    while (action_index < program.endpoint_action_count) : (action_index += 1) {
        const action = program.endpoint_actions[action_index];
        try testing.expect(action.key.raw_diagram_index < program.raw_diagram_count);
        try testing.expect(action.key.input_word_count != 0);
        try testing.expect(action.key.boundary_signature != 0);
        var other_index: u16 = action_index + 1;
        while (other_index < program.endpoint_action_count) : (other_index += 1) {
            try testing.expect(!tensorEndpointActionKeyEql(action.key, program.endpoint_actions[other_index].key));
        }
    }

    var raw_index: u8 = 0;
    while (raw_index < program.raw_diagram_count) : (raw_index += 1) {
        const output_action = tensorOnlyProjectedRawAction(&program, raw_index);
        try testing.expectEqual(TensorEndpointSide.output, output_action.key.side);
        try testing.expect(output_action.key.raw_diagram_index < program.raw_diagram_count);
        try testing.expect(output_action.word_count != 0);
    }
}

test "projector constructor indexes tensor-only candidate-pair term windows" {
    const testing = std.testing;
    const program = try compileGeneralTensorOnlyBrauerProgram(tensorOnlyTestChannel(1, 1, 2));

    var covered: u32 = 0;
    var active_index: u16 = 0;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const pair_slot = @as(usize, row) * max_tensor_pivots + column;
            const pair_index = program.pair_term_indices[@as(usize, row) * max_tensor_pivots + column];
            if (pair_index.term_count == 0) continue;
            try testing.expect(active_index < program.active_pair_term_count);
            try testing.expectEqual(@as(u16, @intCast(pair_slot)), program.active_pair_term_indices[active_index]);
            try testing.expectEqual(pair_slot, try tensorOnlyActivePairSlotForTerm(&program, pair_index.first_term));
            try testing.expectEqual(pair_slot, try tensorOnlyActivePairSlotForTerm(&program, pair_index.first_term + pair_index.term_count - 1));
            try testing.expectEqual(covered, pair_index.first_term);
            covered += pair_index.term_count;
            active_index += 1;
        }
    }
    try testing.expectEqual(active_index, program.active_pair_term_count);
    try testing.expectEqual(@as(u32, program.term_count), covered);
    try testing.expect(program.term_count != 0);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    _ = try appendTensorOnlyProgramTerm(testing.allocator, &atoms, &program, 0);
    try testing.expect(atoms.items.len != 0);
}

test "projector constructor merges tensor-only action pair streams into primitive spans" {
    const testing = std.testing;
    var program = try compileGeneralTensorOnlyBrauerProgram(tensorOnlyTestChannel(1, 1, 2));
    defer program.deinit();

    try testing.expectEqual(@as(usize, program.term_count), program.merged_terms.len);

    var active_index: u16 = 0;
    while (active_index < program.active_pair_term_count) : (active_index += 1) {
        const pair_slot = program.active_pair_term_indices[active_index];
        const row: u8 = @intCast(pair_slot / max_tensor_pivots);
        const column: u8 = @intCast(pair_slot % max_tensor_pivots);
        const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
        const action_count = try countTensorOnlyCandidatePairActionTerms(
            &program,
            program.candidates[program.pivots[row]],
            program.candidates[program.pivots[column]],
            coefficient,
        );
        const pair_index = program.pair_term_indices[pair_slot];
        try testing.expect(pair_index.term_count <= action_count);
        try testing.expect(@as(usize, pair_index.first_term) + pair_index.term_count <= program.merged_terms.len);
        const term = program.merged_terms[pair_index.first_term + pair_index.term_count - 1];
        try testing.expect(term.atom_count != 0);
    }
}

test "projector constructor budgets tensor-only action pair work before construction" {
    const testing = std.testing;
    var words = [_]TensorEndpointActionWord{.{ .word = .{ .coefficient = Rational.one() } }} ** max_tensor_endpoint_action_words;
    var program: TensorOnlyProgram = .{
        .channel = tensorOnlyTestChannel(1, 1, 0),
        .raw_diagram_count = 1,
        .endpoint_action_count = 1,
        .candidate_count = 1,
        .pivot_count = max_tensor_pivots,
    };
    program.endpoint_actions[0] = .{
        .word_count = max_tensor_endpoint_action_words,
        .words = words[0..],
    };
    program.projected_raw_action_indices[0] = 0;
    try program.candidates[0].append(.{ .kind = .raw_brauer_diagram, .candidate_index = 0 });
    var pivot_index: u8 = 0;
    while (pivot_index < program.pivot_count) : (pivot_index += 1) {
        program.pivots[pivot_index] = 0;
        var inverse_column: u8 = 0;
        while (inverse_column < program.pivot_count) : (inverse_column += 1) {
            program.inverse_gram[@as(usize, pivot_index) * max_tensor_pivots + inverse_column] = Rational.one();
        }
    }

    try testing.expectError(error.ProjectorProgramTooLarge, budgetTensorOnlyPairTermsBeforeConstruction(&program));
}

test "projector constructor routes former tensor channel kinds through general tensor-only compiler" {
    const testing = std.testing;
    const young_spec: StructuralProjectorSpec = .{
        .operator_id = 2001,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .output = .{
            .index = 3,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
    };
    const pairing_spec: StructuralProjectorSpec = .{
        .operator_id = 2002,
        .orthogonal_dimension = 10,
        .left = young_spec.left,
        .right = young_spec.right,
        .output = .{ .index = 4 },
    };
    const contraction_spec: StructuralProjectorSpec = .{
        .operator_id = 2003,
        .orthogonal_dimension = 10,
        .left = young_spec.left,
        .right = .{
            .index = 5,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .output = young_spec.left,
    };

    const young_channel = try tensorCompilerChannelFromStructural(young_spec);
    const pairing_channel = try tensorCompilerChannelFromStructural(pairing_spec);
    const contraction_channel = try tensorCompilerChannelFromStructural(contraction_spec);
    try testing.expectEqual(TensorChannelKind.young_output, try tensorChannelKind(young_channel));
    try testing.expectEqual(TensorChannelKind.scalar_pairing, try tensorChannelKind(pairing_channel));
    try testing.expectEqual(TensorChannelKind.tensor_contraction, try tensorChannelKind(contraction_channel));

    var young_cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer young_cache.deinit();
    try testing.expect((try young_cache.termCount(young_spec)) != 0);
    try testing.expectEqual(@as(usize, 1), young_cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), young_cache.vector_entries.items.len);
    try testing.expect(young_cache.tensor_only_entries.items[0].program.endpoint_action_count != 0);

    var pairing_cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer pairing_cache.deinit();
    try testing.expect((try pairing_cache.termCount(pairing_spec)) != 0);
    try testing.expectEqual(@as(usize, 1), pairing_cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), pairing_cache.vector_entries.items.len);
    try testing.expect(pairing_cache.tensor_only_entries.items[0].program.endpoint_action_count != 0);

    var contraction_cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer contraction_cache.deinit();
    try testing.expect((try contraction_cache.termCount(contraction_spec)) != 0);
    try testing.expectEqual(@as(usize, 1), contraction_cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), contraction_cache.vector_entries.items.len);
    try testing.expect(contraction_cache.tensor_only_entries.items[0].program.endpoint_action_count != 0);
}

test "projector constructor keeps raw-budget boundary-eight tensor channels on live route" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 2010,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .output = .{
            .index = 3,
            .young_row_count = 1,
            .young_rows = .{ 4, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 4,
        },
    };
    const channel = try tensorCompilerChannelFromStructural(spec);
    const tensor_channel = try liveTensorOnlyChannelFromCompilerChannel(channel);

    try testing.expectEqual(@as(u8, 4), tensor_channel.input_slot_count);
    try testing.expectEqual(@as(u8, 4), tensor_channel.output_slot_count);
    try budgetTensorOnlyRawDiagramsBeforeEnumeration(tensor_channel);
}

test "projector constructor keys tensor-only cache by Young endpoint shape" {
    const testing = std.testing;
    const symmetric_spec: StructuralProjectorSpec = .{
        .operator_id = 2011,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .output = .{ .index = 3 },
    };
    const exterior_spec: StructuralProjectorSpec = .{
        .operator_id = 2012,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 2,
            .young_rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .right = .{
            .index = 2,
            .young_row_count = 2,
            .young_rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .output = .{ .index = 3 },
    };

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    try testing.expect((try cache.termCount(symmetric_spec)) != 0);
    try testing.expect((try cache.termCount(exterior_spec)) != 0);
    try testing.expectEqual(@as(usize, 2), cache.tensor_only_entries.items.len);
    try testing.expect(!structuralProgramKeyEql(cache.tensor_only_entries.items[0].key, cache.tensor_only_entries.items[1].key));
    try testing.expectEqual(@as(u8, 1), cache.tensor_only_entries.items[0].key.source_young_row_count);
    try testing.expectEqual(@as(u8, 2), cache.tensor_only_entries.items[1].key.source_young_row_count);
}

test "projector constructor direct tensor helpers match general tensor-only compiler" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 2013,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .output = .{
            .index = 3,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
    };
    const channel = try tensorCompilerChannelFromStructural(spec);
    const tensor_channel = try liveTensorOnlyChannelFromCompilerChannel(channel);
    var general_program = try compileGeneralTensorOnlyBrauerProgram(tensor_channel);
    defer general_program.deinit();

    try testing.expectEqual(general_program.term_count, try tensorChannelTermCount(channel));

    var general_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer general_atoms.deinit(testing.allocator);
    const general_coefficient = try appendTensorOnlyProgramTerm(testing.allocator, &general_atoms, &general_program, 0);

    var direct_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer direct_atoms.deinit(testing.allocator);
    const direct_coefficient = try appendTensorChannelTerm(testing.allocator, &direct_atoms, channel, 0);

    try testing.expectEqual(general_coefficient, direct_coefficient);
    try testing.expectEqualDeep(general_atoms.items, direct_atoms.items);
}

test "projector constructor derives mixed endpoint slot layout before streaming" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 2003,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .output = .{
            .index = 3,
            .young_row_count = 1,
            .young_rows = .{ 3, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
    };
    const tensor_channel = try tensorOnlyChannelFromCompilerChannel(try tensorCompilerChannelFromStructural(spec));
    try testing.expectEqual(@as(u8, 2), tensor_channel.left.layout.slot_count);
    try testing.expectEqual(tensorFormRankBlock(spec.left.index, 2), tensor_channel.left.layout.slots[0].block);
    try testing.expectEqual(tensorFormRankBlock(spec.left.index, 2), tensor_channel.left.layout.slots[1].block);
    try testing.expectEqual(@as(u8, 0), tensor_channel.left.layout.slots[0].slot);
    try testing.expectEqual(@as(u8, 1), tensor_channel.left.layout.slots[1].slot);
}

test "projector constructor rejects non-middle Hodge tensor-only endpoint" {
    const testing = std.testing;
    var channel = tensorOnlyTestChannel(1, 1, 2);
    channel.output.kind = .hodge_form;
    channel.output.duality = .self_dual;

    try testing.expect(tensorOnlyEndpointLiveRouteSupported(channel.output));
    try testing.expectError(error.UnsupportedTensorBridge, compileGeneralTensorOnlyBrauerProgram(channel));
}

test "projector constructor streams Hodge endpoint actions as compact tensor-only atoms" {
    const testing = std.testing;
    var channel = tensorOnlyTestChannel(1, 1, 2);
    channel.dimension = 4;
    channel.output.kind = .hodge_form;
    channel.output.row_count = 2;
    channel.output.rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 };
    channel.output.column_count = 1;
    channel.output.column_heights = .{ 2, 0, 0, 0, 0, 0, 0, 0 };
    channel.output.duality = .self_dual;
    channel.output.form_rank = 2;
    channel.output.form_profile = @as(u128, 1) << 4;
    channel.output.form_mask = @as(u64, 1) << 1;

    var program = try compileGeneralTensorOnlyBrauerProgram(channel);
    defer program.deinit();

    const output_projector = tensorOnlyProgramOutputProjector(&program);
    try testing.expectEqual(@as(u8, 2), output_projector.operator_count);
    try testing.expectEqual(TensorEndpointOperatorKind.young_column_antisymmetrizer, output_projector.operators[0].kind);
    try testing.expectEqual(@as(u8, 2), output_projector.operators[0].slot_count);
    try testing.expectEqual(TensorEndpointOperatorKind.hodge_projector, output_projector.operators[1].kind);
    try testing.expectEqual(@as(u8, 0), output_projector.trace_free.basis_count);

    try testing.expect(program.term_count != 0);
    const projected = tensorOnlyProjectedRawAction(&program, 0);
    var identity_branch_count: u8 = 0;
    var hodge_branch_count: u8 = 0;
    var action_word_index: u8 = 0;
    while (action_word_index < projected.word_count) : (action_word_index += 1) {
        const action_word = projected.words[action_word_index];
        if (action_word.hodge_count == 0) {
            identity_branch_count += 1;
        } else {
            hodge_branch_count += 1;
            try testing.expectEqual(@as(u8, 1), action_word.hodge_count);
            try testing.expectEqual(TensorEndpointSide.output, action_word.hodge_actions[0].side);
            try testing.expectEqual(rendering.DualityTag.self_dual, action_word.hodge_actions[0].duality);
        }
    }
    try testing.expect(identity_branch_count != 0);
    try testing.expectEqual(identity_branch_count, hodge_branch_count);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var saw_hodge = false;
    var term_index: u16 = 0;
    while (term_index < program.term_count and !saw_hodge) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try appendTensorOnlyProgramTerm(testing.allocator, &atoms, &program, term_index);
        for (atoms.items) |atom| {
            if (std.meta.activeTag(atom) == .hodge_star) saw_hodge = true;
        }
    }
    try testing.expect(saw_hodge);
}

test "projector constructor routes Hodge source scalar pairings through tensor-only cache" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 2031,
        .orthogonal_dimension = 4,
        .left = .{
            .index = 1,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
            .form_duality = .self_dual,
        },
        .right = .{
            .index = 2,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
            .form_duality = .self_dual,
        },
        .output = .{ .index = 3 },
    };

    const channel = try tensorCompilerChannelFromStructural(spec);
    try testing.expectError(error.UnsupportedTensorBridge, tensorChannelKind(channel));
    const tensor_channel = try liveTensorOnlyChannelFromCompilerChannel(channel);
    var program = try compileGeneralTensorOnlyBrauerProgram(tensor_channel);
    defer program.deinit();
    try testing.expect(program.term_count != 0);
    try testing.expectEqual(TensorEndpointOperatorKind.hodge_projector, tensorOnlyProgramLeftProjector(&program).operators[1].kind);
    try testing.expectEqual(TensorEndpointOperatorKind.hodge_projector, tensorOnlyProgramRightProjector(&program).operators[1].kind);

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    try testing.expectEqual(program.term_count, try cache.termCount(spec));
    try testing.expectEqual(@as(usize, 1), cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), cache.vector_entries.items.len);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var saw_hodge = false;
    var term_index: u16 = 0;
    while (term_index < program.term_count and !saw_hodge) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try appendTensorOnlyProgramTerm(testing.allocator, &atoms, &program, term_index);
        for (atoms.items) |atom| {
            if (std.meta.activeTag(atom) == .hodge_star) saw_hodge = true;
        }
    }
    try testing.expect(saw_hodge);
}

test "projector constructor routes Hodge output channels without channel-kind formulas" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 2032,
        .orthogonal_dimension = 4,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .output = .{
            .index = 3,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
            .form_duality = .self_dual,
        },
    };

    const channel = try tensorCompilerChannelFromStructural(spec);
    try testing.expectError(error.UnsupportedTensorBridge, tensorChannelKind(channel));

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    const term_count = try cache.termCount(spec);
    try testing.expect(term_count != 0);
    try testing.expectEqual(@as(usize, 1), cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), cache.vector_entries.items.len);
    try testing.expectEqual(term_count, structuralProjectorTermCount(spec));

    const program = cache.tensor_only_entries.items[0].program;
    try testing.expectEqual(TensorEndpointOperatorKind.hodge_projector, tensorOnlyProgramOutputProjector(&program).operators[1].kind);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var saw_hodge = false;
    var term_index: u16 = 0;
    while (term_index < term_count and !saw_hodge) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try cache.appendTerm(&atoms, spec, term_index);
        for (atoms.items) |atom| {
            if (std.meta.activeTag(atom) == .hodge_star) saw_hodge = true;
        }
    }
    try testing.expect(saw_hodge);

    saw_hodge = false;
    term_index = 0;
    while (term_index < term_count and !saw_hodge) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try appendStructuralProjectorTerm(testing.allocator, &atoms, spec, term_index);
        for (atoms.items) |atom| {
            if (std.meta.activeTag(atom) == .hodge_star) saw_hodge = true;
        }
    }
    try testing.expect(saw_hodge);
}

test "projector constructor derives omitted single-form profile for tensor-only Hodge endpoint" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 2033,
        .orthogonal_dimension = 4,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .output = .{
            .index = 3,
            .form_count = 1,
            .form_rank = 2,
            .form_duality = .self_dual,
        },
    };

    const channel = try tensorCompilerChannelFromStructural(spec);
    try testing.expectError(error.UnsupportedTensorBridge, tensorChannelKind(channel));
    const tensor_channel = try liveTensorOnlyChannelFromCompilerChannel(channel);
    try testing.expectEqual(TensorOnlyEndpointKind.hodge_form, tensor_channel.output.kind);
    try testing.expectEqual(@as(u8, 2), tensor_channel.output.slot_count);
    try testing.expectEqual(@as(u128, 1) << 4, tensor_channel.output.form_profile);
    try testing.expectEqual(tensorFormRankBlock(spec.output.index, 2), tensor_channel.output.layout.slots[0].block);

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    const term_count = try cache.termCount(spec);
    try testing.expect(term_count != 0);
    try testing.expectEqual(@as(usize, 1), cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), cache.vector_entries.items.len);
}

test "projector constructor rejects inconsistent single-form endpoint metadata" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 2034,
        .orthogonal_dimension = 4,
        .left = .{
            .index = 1,
            .form_count = 1,
            .form_rank = 2,
            .form_profile = @as(u128, 1) << 8,
        },
        .right = .{ .index = 2 },
        .output = .{ .index = 3 },
    };

    try testing.expectError(error.InvalidFormProfile, tensorCompilerChannelFromStructural(spec));
    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    try testing.expectError(error.InvalidFormProfile, cache.termCount(spec));
}

test "projector constructor rejects mixed-form Hodge as tensor-only endpoint factor" {
    const testing = std.testing;
    const profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4);
    const spec: StructuralProjectorSpec = .{
        .operator_id = 2035,
        .orthogonal_dimension = 4,
        .left = .{
            .index = 1,
            .form_profile = profile,
            .form_mask = 0b11,
            .form_count = 2,
            .form_duality = .self_dual,
        },
        .right = .{ .index = 2 },
        .output = .{ .index = 3 },
    };

    const channel = try tensorCompilerChannelFromStructural(spec);
    try testing.expectError(error.UnsupportedTensorBridge, liveTensorOnlyChannelFromCompilerChannel(channel));
    try testing.expectError(error.UnsupportedTensorBridge, tensorChannelTermCount(channel));
    var direct_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer direct_atoms.deinit(testing.allocator);
    try testing.expectError(error.UnsupportedTensorBridge, appendTensorChannelTerm(testing.allocator, &direct_atoms, channel, 0));
    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    try testing.expectError(error.UnsupportedTensorBridge, cache.termCount(spec));
    try testing.expectEqual(@as(u16, 0), structuralProjectorTermCount(spec));
}

test "projector constructor routes explicit exterior Young duality through tensor-only Hodge" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 2036,
        .orthogonal_dimension = 4,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .output = .{
            .index = 3,
            .young_row_count = 2,
            .young_rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
            .form_duality = .self_dual,
        },
    };

    const channel = try tensorCompilerChannelFromStructural(spec);
    try testing.expectError(error.UnsupportedTensorBridge, tensorChannelKind(channel));
    const tensor_channel = try liveTensorOnlyChannelFromCompilerChannel(channel);
    try testing.expectEqual(TensorOnlyEndpointKind.hodge_form, tensor_channel.output.kind);
    try testing.expectEqual(@as(u128, 1) << 4, tensor_channel.output.form_profile);
    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    try testing.expect((try cache.termCount(spec)) != 0);
    try testing.expectEqual(@as(usize, 1), cache.tensor_only_entries.items.len);
}

test "projector constructor rejects form metadata on non-exterior Young endpoint" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 2037,
        .orthogonal_dimension = 6,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
            .form_count = 1,
            .form_rank = 2,
        },
        .right = .{ .index = 2 },
        .output = .{ .index = 3 },
    };

    try testing.expectError(error.InvalidFormProfile, tensorCompilerChannelFromStructural(spec));
    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    try testing.expectError(error.InvalidFormProfile, cache.termCount(spec));
}

test "projector constructor streams compact Hodge primitive atoms" {
    const testing = std.testing;
    var term = try vectorBrauerTerm(Rational.one());
    try vectorBrauerTermHodgeStar(&term, 10, 11);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    const coefficient = try appendVectorBrauerTermAtoms(testing.allocator, &atoms, term);
    try testing.expectEqual(@as(i32, 1), coefficient.numerator);
    try testing.expectEqual(@as(usize, 1), atoms.items.len);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).hodge_star, std.meta.activeTag(atoms.items[0]));
    try testing.expectEqual(@as(rendering.IndexBlockId, 10), atoms.items[0].hodge_star.input);
    try testing.expectEqual(@as(rendering.IndexBlockId, 11), atoms.items[0].hodge_star.output);
}

test "projector constructor streams tensor-only Brauer terms as primitive vector atoms" {
    const testing = std.testing;
    const program = try compileTensorOnlyBrauerProgram(tensorOnlyTestChannel(1, 1, 2));
    try testing.expect(program.pivot_count != 0);
    try testing.expect(program.term_count != 0);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    const coefficient = try appendTensorOnlyProgramTerm(testing.allocator, &atoms, &program, 0);
    try testing.expect(coefficient.numerator != 0);
    try testing.expect(atoms.items.len != 0);
    for (atoms.items) |atom| {
        switch (atom) {
            .vector_slot_delta, .vector_slot_metric => {},
            else => return error.UnsupportedTensorBridge,
        }
    }
}

test "projector constructor streams tensor-only scalar pairing terms as primitive metrics" {
    const testing = std.testing;
    const program = try compileTensorOnlyBrauerProgram(tensorOnlyTestChannel(1, 1, 0));
    try testing.expectEqual(@as(u16, 1), program.term_count);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    const coefficient = try appendTensorOnlyProgramTerm(testing.allocator, &atoms, &program, 0);
    try testing.expectEqual(@as(i64, 1), coefficient.numerator);
    try testing.expectEqual(@as(i64, 10), coefficient.denominator);
    try testing.expectEqual(@as(usize, 2), atoms.items.len);
    for (atoms.items) |atom| switch (atom) {
        .vector_slot_metric => {},
        else => return error.ExpectedVectorSlotPrimitive,
    };
}

test "projector constructor streams tensor-only contraction terms as primitive delta and metric atoms" {
    const testing = std.testing;
    const program = try compileTensorOnlyBrauerProgram(tensorOnlyTestChannel(1, 2, 1));
    try testing.expect(program.term_count != 0);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    _ = try appendTensorOnlyProgramTerm(testing.allocator, &atoms, &program, 0);
    var saw_delta = false;
    var saw_metric = false;
    for (atoms.items) |atom| switch (atom) {
        .vector_slot_delta => saw_delta = true,
        .vector_slot_metric => saw_metric = true,
        else => return error.ExpectedVectorSlotPrimitive,
    };
    try testing.expect(saw_delta);
    try testing.expect(saw_metric);
}

test "projector constructor streams descriptor-owned tensor-only routes as primitives only" {
    try expectStructuralTensorOnlyPrimitiveRoute(.{
        .operator_id = 2040,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .output = .{ .index = 3 },
    }, false);

    try expectStructuralTensorOnlyPrimitiveRoute(.{
        .operator_id = 2041,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .output = .{
            .index = 3,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
    }, false);

    try expectStructuralTensorOnlyPrimitiveRoute(.{
        .operator_id = 2042,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .output = .{
            .index = 3,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
    }, false);

    try expectStructuralTensorOnlyPrimitiveRoute(.{
        .operator_id = 2043,
        .orthogonal_dimension = 4,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .output = .{
            .index = 3,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
            .form_duality = .self_dual,
        },
    }, true);

    try expectStructuralTensorOnlyPrimitiveRoute(.{
        .operator_id = 2044,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
        },
        .right = .{
            .index = 2,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
        },
        .output = .{ .index = 3 },
    }, false);

    try expectStructuralTensorOnlyPrimitiveRoute(.{
        .operator_id = 2045,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4),
            .form_mask = 0b11,
            .form_count = 2,
        },
        .right = .{ .index = 2 },
        .output = .{
            .index = 3,
            .young_row_count = 2,
            .young_rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
    }, false);

    try expectStructuralTensorOnlyPrimitiveRoute(.{
        .operator_id = 2046,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 2,
            .young_rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
        .right = .{ .index = 2 },
        .output = .{
            .index = 3,
            .form_profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4),
            .form_mask = 0b11,
            .form_count = 2,
        },
    }, false);

    try expectStructuralTensorOnlyPrimitiveRoute(.{
        .operator_id = 2047,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 1, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 1,
        },
        .output = .{
            .index = 3,
            .form_profile = @as(u128, 2) << 0,
            .form_mask = 0b1,
            .form_count = 2,
        },
    }, false);
}

test "projector constructor tensor-only direct Gram graph matches projected action buffers" {
    const testing = std.testing;
    const channel: TensorOnlyChannel = .{
        .operator_id = 92,
        .dimension = 10,
        .left = tensorOnlyHookTestEndpoint(.left),
        .right = tensorOnlyTestEndpoint(.right, 0),
        .output = tensorOnlyHookTestEndpoint(.output),
        .input_slot_count = 3,
        .output_slot_count = 3,
    };
    var program = try compileGeneralTensorOnlyBrauerProgram(channel);
    defer program.deinit();

    var raw_left: u8 = 0;
    while (raw_left < program.raw_diagram_count) : (raw_left += 1) {
        var raw_right: u8 = 0;
        while (raw_right < program.raw_diagram_count) : (raw_right += 1) {
            const left_action = tensorOnlyProjectedRawAction(&program, raw_left);
            const right_action = tensorOnlyProjectedRawAction(&program, raw_right);
            var expected = Rational.zero();
            var left_index: u8 = 0;
            while (left_index < left_action.word_count) : (left_index += 1) {
                var right_index: u8 = 0;
                while (right_index < right_action.word_count) : (right_index += 1) {
                    const left_word = left_action.words[left_index];
                    const right_word = right_action.words[right_index];
                    if (!tensorEndpointActionWordHodgeEql(left_word, right_word)) continue;
                    expected = try expected.add(try tensorContractionWordInnerProduct(
                        program.channel.dimension,
                        program.channel.input_slot_count,
                        program.channel.output_slot_count,
                        left_word.word,
                        right_word.word,
                    ));
                }
            }
            const actual = try tensorEndpointActionInnerProduct(
                program.channel.dimension,
                program.channel.input_slot_count,
                program.channel.output_slot_count,
                left_action,
                right_action,
            );
            try testing.expect(rationalValueEql(expected, actual));
        }
    }
}

test "projector constructor stores compact candidate words without allocation" {
    const testing = std.testing;

    var word: ProjectorCandidateWord = .{};
    try word.append(.{
        .kind = .gamma_rank_split,
        .input_block = 11,
        .output_block = 12,
        .auxiliary_block = 13,
        .rank = 3,
        .auxiliary_rank = 4,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });
    try word.append(.{
        .kind = .form_delta,
        .input_block = 21,
        .output_block = 22,
    });

    try testing.expectEqual(@as(u8, 2), word.count);
    try testing.expectEqual(ProjectorPrimitiveKind.gamma_rank_split, word.slots[0].kind);
    try testing.expectEqual(@as(rendering.IndexBlockId, 11), word.slots[0].input_block);
    try testing.expectEqual(@as(rendering.IndexBlockId, 13), word.slots[0].auxiliary_block);
    try testing.expectEqual(ProjectorPrimitiveKind.form_delta, word.slots[1].kind);

    var buffer: ProjectorCandidateBuffer = .{};
    try buffer.append(word);
    try testing.expectEqual(@as(u8, 1), buffer.count);
    try testing.expectEqual(@as(u8, 2), buffer.words[0].count);

    var full_word: ProjectorCandidateWord = .{};
    var slot_index: u8 = 0;
    while (slot_index < max_program_primitives) : (slot_index += 1) {
        try full_word.append(.{ .kind = .form_delta });
    }
    try testing.expectError(error.ProjectorWordTooLarge, full_word.append(.{ .kind = .form_delta }));

    var full_buffer: ProjectorCandidateBuffer = .{};
    var candidate_index: u8 = 0;
    while (candidate_index < max_program_candidates) : (candidate_index += 1) {
        try full_buffer.append(.{});
    }
    try testing.expectError(error.UnsupportedTensorBrauerCandidateCap, full_buffer.append(.{}));
}

test "projector constructor wraps tensor-only Brauer channels as candidate words" {
    const testing = std.testing;

    const young_spec: StructuralProjectorSpec = .{
        .operator_id = 31,
        .orthogonal_dimension = 9,
        .left = .{
            .index = 1,
            .form_profile = 1,
            .form_mask = 1,
            .form_count = 1,
            .form_rank = 1,
        },
        .right = .{
            .index = 2,
            .form_profile = 1,
            .form_mask = 1,
            .form_count = 1,
            .form_rank = 1,
        },
        .output = .{
            .index = 3,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
    };
    const young_channel = try tensorCompilerChannelFromStructural(young_spec);
    const young_program = try compileDiagnosticFallbackTensorChannelProgram(young_channel);
    try testing.expectEqual(CachedVectorProgramKind.projector, young_program.kind);
    try testing.expectEqual(young_program.vector_program.candidate_count, young_program.candidate_count);
    try testing.expectEqual(@as(u8, 3), young_program.words[0].primitive_count);
    try testing.expectEqual(TensorPrimitiveKind.form_bridge, young_program.words[0].primitives[0].kind);
    try testing.expectEqual(@as(u8, 0), young_program.words[0].primitives[0].candidate_index);
    try testing.expectEqual(TensorPrimitiveKind.form_bridge, young_program.words[0].primitives[1].kind);
    try testing.expectEqual(@as(u8, 1), young_program.words[0].primitives[1].candidate_index);
    try testing.expectEqual(TensorPrimitiveKind.vector_young_output, young_program.words[0].primitives[2].kind);
    try testing.expectEqual(@as(u8, 0), young_program.words[0].primitives[2].candidate_index);

    const pairing_spec: StructuralProjectorSpec = .{
        .operator_id = 32,
        .orthogonal_dimension = 9,
        .left = .{
            .index = 4,
            .young_row_count = 2,
            .young_rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .right = .{
            .index = 5,
            .young_row_count = 2,
            .young_rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .output = .{ .index = 6 },
    };
    const pairing_channel = try tensorCompilerChannelFromStructural(pairing_spec);
    const pairing_program = try compileDiagnosticFallbackTensorChannelProgram(pairing_channel);
    try testing.expectEqual(CachedVectorProgramKind.pairing, pairing_program.kind);
    try testing.expectEqual(pairing_program.vector_program.candidate_count, pairing_program.candidate_count);
    try testing.expectEqual(@as(u8, 3), pairing_program.words[0].primitive_count);
    try testing.expectEqual(TensorPrimitiveKind.form_bridge, pairing_program.words[0].primitives[0].kind);
    try testing.expectEqual(@as(u8, 0), pairing_program.words[0].primitives[0].candidate_index);
    try testing.expectEqual(TensorPrimitiveKind.form_bridge, pairing_program.words[0].primitives[1].kind);
    try testing.expectEqual(@as(u8, 2), pairing_program.words[0].primitives[1].candidate_index);
    try testing.expectEqual(TensorPrimitiveKind.vector_young_pairing, pairing_program.words[0].primitives[2].kind);
}

test "projector constructor compiles tensor contraction channels through Brauer Gram" {
    const testing = std.testing;

    const contraction_spec: StructuralProjectorSpec = .{
        .operator_id = 321,
        .orthogonal_dimension = 9,
        .left = .{
            .index = 1,
            .form_profile = 1,
            .form_mask = 1,
            .form_count = 1,
            .form_rank = 1,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .output = .{
            .index = 3,
            .form_profile = 1,
            .form_mask = 1,
            .form_count = 1,
            .form_rank = 1,
        },
    };
    const channel = try tensorCompilerChannelFromStructural(contraction_spec);
    try testing.expectEqual(TensorChannelKind.tensor_contraction, try tensorChannelKind(channel));
    const program = try compileDiagnosticFallbackTensorChannelProgram(channel);
    try testing.expectEqual(CachedVectorProgramKind.contraction, program.kind);
    try testing.expect(program.candidate_count != 0);
    try testing.expect(program.term_count != 0);
    try testing.expectEqual(@as(u8, 3), program.words[0].primitive_count);
    try testing.expectEqual(TensorPrimitiveKind.form_bridge, program.words[0].primitives[0].kind);
    try testing.expectEqual(@as(u8, 0), program.words[0].primitives[0].candidate_index);
    try testing.expectEqual(TensorPrimitiveKind.form_bridge, program.words[0].primitives[1].kind);
    try testing.expectEqual(@as(u8, 2), program.words[0].primitives[1].candidate_index);
    try testing.expectEqual(TensorPrimitiveKind.vector_tensor_contraction, program.words[0].primitives[2].kind);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    const coefficient = try appendTensorChannelProgramTerm(testing.allocator, &atoms, program, 0);
    try testing.expect(coefficient.numerator != 0);
    var saw_delta = false;
    var saw_metric = false;
    for (atoms.items) |atom| switch (atom) {
        .vector_slot_delta => saw_delta = true,
        .vector_slot_metric => saw_metric = true,
        else => return error.UnexpectedTensorContractionAtom,
    };
    try testing.expect(saw_delta);
    try testing.expect(saw_metric);

    const double_contraction_spec: StructuralProjectorSpec = .{
        .operator_id = 322,
        .orthogonal_dimension = 9,
        .left = .{
            .index = 4,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .right = .{
            .index = 5,
            .young_row_count = 1,
            .young_rows = .{ 3, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
        .output = .{
            .index = 6,
            .form_profile = 1,
            .form_mask = 1,
            .form_count = 1,
            .form_rank = 1,
        },
    };
    const double_channel = try tensorCompilerChannelFromStructural(double_contraction_spec);
    const double_spec = tensorContractionSpecFromChannel(double_channel).?;
    try testing.expectEqual(@as(u8, 2), double_spec.contraction_count);
    const double_program = try compileDiagnosticFallbackTensorChannelProgram(double_channel);
    try testing.expectEqual(CachedVectorProgramKind.contraction, double_program.kind);
    try testing.expect(double_program.candidate_count != 0);
    try testing.expect(double_program.term_count != 0);

    atoms.clearRetainingCapacity();
    const double_coefficient = try appendTensorChannelProgramTerm(testing.allocator, &atoms, double_program, 0);
    try testing.expect(double_coefficient.numerator != 0);
    var metric_count: u8 = 0;
    for (atoms.items) |atom| switch (atom) {
        .vector_slot_delta => {},
        .vector_slot_metric => metric_count += 1,
        else => return error.UnexpectedTensorContractionAtom,
    };
    try testing.expect(metric_count >= 2);
}

test "projector constructor computes vector-backed channel Gram through tensor candidate words" {
    const testing = std.testing;

    const young_spec: StructuralProjectorSpec = .{
        .operator_id = 33,
        .orthogonal_dimension = 9,
        .left = .{
            .index = 1,
            .form_profile = 1,
            .form_mask = 1,
            .form_count = 1,
            .form_rank = 1,
        },
        .right = .{
            .index = 2,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
        },
        .output = .{
            .index = 3,
            .young_row_count = 2,
            .young_rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
    };
    try expectTensorWordGramMatchesVectorGram(try compileDiagnosticFallbackTensorChannelProgram(try tensorCompilerChannelFromStructural(young_spec)));

    const pairing_spec: StructuralProjectorSpec = .{
        .operator_id = 34,
        .orthogonal_dimension = 9,
        .left = .{
            .index = 4,
            .young_row_count = 2,
            .young_rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
        .right = .{
            .index = 5,
            .young_row_count = 2,
            .young_rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
        .output = .{ .index = 6 },
    };
    try expectTensorWordGramMatchesVectorGram(try compileDiagnosticFallbackTensorChannelProgram(try tensorCompilerChannelFromStructural(pairing_spec)));
    _ = testing;
}

test "projector constructor routes structural Clifford channels through tensor candidate words" {
    const testing = std.testing;
    const form_spec: TensorFormProjectionSpec = .{
        .operator_id = 35,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 0,
        .input_form_mask = 1,
        .output_form_profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4),
        .output_form_count = 2,
        .output_form_rank = 1,
        .chirality = 1,
    };
    const structural_spec = structuralProjectorSpecFromTensorForm(form_spec);
    const channel = try tensorCompilerChannelFromStructural(structural_spec);
    try testing.expectEqual(TensorChannelKind.spinor_clifford_bridge, try tensorChannelKind(channel));

    const tensor_program = try compileDiagnosticFallbackTensorChannelProgram(channel);
    const structural_program = try compileStructuralProjectorProgram(structural_spec);
    try testing.expectEqual(CachedVectorProgramKind.structural, tensor_program.kind);
    try testing.expectEqual(structural_program.candidate_count, tensor_program.candidate_count);
    try testing.expectEqual(@as(u8, 1), tensor_program.words[0].primitive_count);
    try testing.expectEqual(TensorPrimitiveKind.structural_projection, tensor_program.words[0].primitives[0].kind);
    try testing.expectEqual(structural_program.pivot_count, tensor_program.pivot_count);
    try testing.expectEqual(projectorProgramTermCount(structural_program), tensor_program.term_count);

    var pivot_index: u8 = 0;
    while (pivot_index < tensor_program.pivot_count) : (pivot_index += 1) {
        try testing.expectEqual(structural_program.pivots[pivot_index], tensor_program.pivots[pivot_index]);
    }
    var entry_index: usize = 0;
    while (entry_index < @as(usize, tensor_program.pivot_count) * tensor_program.pivot_count) : (entry_index += 1) {
        try testing.expect(rationalValueEql(structural_program.inverse_gram[entry_index], tensor_program.inverse_gram[entry_index]));
    }

    var structural_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer structural_atoms.deinit(testing.allocator);
    var tensor_atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer tensor_atoms.deinit(testing.allocator);
    const structural_coefficient = try appendStructuralProjectorProgramTerm(testing.allocator, &structural_atoms, structural_spec, structural_program, 0);
    const tensor_coefficient = try appendTensorChannelProgramTerm(testing.allocator, &tensor_atoms, tensor_program, 0);
    try testing.expectEqual(rendering.rationalValue(structural_coefficient).numerator, rendering.rationalValue(tensor_coefficient).numerator);
    try testing.expectEqual(rendering.rationalValue(structural_coefficient).denominator, rendering.rationalValue(tensor_coefficient).denominator);
    try testing.expectEqual(structural_atoms.items.len, tensor_atoms.items.len);
    var atom_index: usize = 0;
    while (atom_index < structural_atoms.items.len) : (atom_index += 1) {
        try testing.expectEqual(std.meta.activeTag(structural_atoms.items[atom_index]), std.meta.activeTag(tensor_atoms.items[atom_index]));
    }
}

test "projector constructor keeps spinor Clifford production on structural cache" {
    const testing = std.testing;
    const form_spec: TensorFormProjectionSpec = .{
        .operator_id = 36,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 0,
        .input_form_mask = 1,
        .output_form_profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4),
        .output_form_count = 2,
        .output_form_rank = 1,
        .chirality = 1,
    };
    const structural_spec = structuralProjectorSpecFromTensorForm(form_spec);
    const channel = try tensorCompilerChannelFromStructural(structural_spec);
    try testing.expectEqual(TensorChannelKind.spinor_clifford_bridge, try tensorChannelKind(channel));
    try testing.expect(tensorChannelUsesDirectStructuralProgram(channel));

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    try testing.expectEqual(@as(usize, 0), cache.entryCount());
    try testing.expectEqual(@as(usize, 0), cache.tensor_entries.items.len);

    const count = try cache.termCount(structural_spec);
    try testing.expectEqual(@as(u16, 1), count);
    try testing.expectEqual(@as(usize, 1), cache.entryCount());
    try testing.expectEqual(@as(usize, 0), cache.tensor_entries.items.len);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    _ = try cache.appendTerm(&atoms, structural_spec, 0);
    try testing.expect(atoms.items.len != 0);
    try testing.expectEqual(@as(usize, 1), cache.entryCount());
    try testing.expectEqual(@as(usize, 0), cache.tensor_entries.items.len);
}

test "projector constructor infers terminal gamma ranks from form profiles" {
    const testing = std.testing;

    try testing.expectEqual(@as(u8, 1), inferTerminalGammaRank(@as(u128, 1) << 4, @as(u128, 1) << 8).?);
    try testing.expectEqual(@as(u8, 2), inferTerminalGammaRank(@as(u128, 1) << 0, @as(u128, 1) << 8).?);
    try testing.expectEqual(@as(u8, 4), inferTerminalGammaRank(@as(u128, 1) << 8, (@as(u128, 1) << 8) | (@as(u128, 1) << 12)).?);
    try testing.expectEqual(@as(u8, 1), inferTerminalGammaRank((@as(u128, 1) << 4) | (@as(u128, 1) << 8), @as(u128, 2) << 8).?);
}

test "projector constructor builds exterior-gamma signatures by finite rank rule" {
    const testing = std.testing;

    const action = makeExteriorGammaAction(10, 3, 3, 2, .none).?;
    try testing.expectEqual(@as(u8, 3), action.input_rank);
    try testing.expectEqual(@as(u8, 3), action.gamma_rank);
    try testing.expectEqual(@as(u8, 2), action.contraction_count);
    try testing.expectEqual(@as(u8, 2), action.output_rank);
    try testing.expectEqual(@as(u1, 1), action.chirality_parity);
    try testing.expectEqual(@as(?ExteriorGammaAction, null), makeExteriorGammaAction(10, 3, 3, 4, .none));

    const insert = primitiveToSignature(.{
        .kind = .gamma_insert,
        .output_block = tensorFormRankBlock(3, 2),
        .rank = 2,
        .output_rank = 2,
        .orthogonal_dimension = 10,
    }).?;
    try testing.expect(signatureEql(insert, insert));
    try testing.expect(signatureChiralityValid(1, 1, insert));
    try testing.expect(!signatureChiralityValid(1, 2, insert));
    try testing.expect(signatureProfileTransition(0, @as(u128, 1) << 4, insert));

    const hodge = primitiveToSignature(.{
        .kind = .hodge_project,
        .input_block = tensorFormRankBlock(1, 3),
        .output_block = tensorFormRankBlock(3, 5),
        .rank = 2,
        .output_rank = 5,
        .orthogonal_dimension = 10,
        .duality = .self_dual,
    }).?;
    try testing.expectEqual(rendering.DualityTag.self_dual, hodge.action.duality);
    try testing.expect(signatureProfileTransition(@as(u128, 1) << 8, @as(u128, 1) << 16, hodge));
}

test "projector constructor enumerates terminal exterior-gamma signatures by rank equation" {
    const testing = std.testing;

    const spec: StructuralProjectorSpec = .{
        .operator_id = 61,
        .orthogonal_dimension = 10,
        .left = .{ .index = 1, .has_spinor = true, .chirality = 1 },
        .right = .{ .index = 2, .has_spinor = true, .chirality = 1 },
        .output = .{ .index = 3 },
    };
    var effects: StructuralPrimitiveEffectBuffer = .{};
    try enumerateTerminalExteriorGammaEffects(spec, .{
        .form_profile = @as(u128, 1) << 8,
        .has_spinor = true,
        .chirality = 1,
    }, .{
        .form_profile = (@as(u128, 1) << 4) | (@as(u128, 1) << 12),
    }, &effects);

    try testing.expectEqual(@as(u8, 3), effects.count);
    try testing.expectEqual(StructuralPrimitiveEffectKind.gamma_rank_split, effects.slots[0].kind);
    try testing.expectEqual(ProjectorPrimitiveKind.gamma_rank_split, effects.slots[0].signature.kind);
    try testing.expectEqual(@as(u8, 3), effects.slots[0].signature.action.input_rank);
    try testing.expectEqual(@as(u8, 1), effects.slots[0].signature.action.gamma_rank);
    try testing.expectEqual(@as(u8, 1), effects.slots[0].signature.action.contraction_count);
    try testing.expectEqual(@as(u8, 2), effects.slots[0].signature.action.output_rank);
    try testing.expectEqual(@as(u8, 4), effects.slots[0].signature.tower_form_rank);
    try testing.expectEqual(@as(u8, 3), effects.slots[1].signature.action.gamma_rank);
    try testing.expectEqual(@as(u8, 2), effects.slots[1].signature.action.contraction_count);
    try testing.expectEqual(@as(u8, 5), effects.slots[2].signature.action.gamma_rank);
    try testing.expectEqual(@as(u8, 3), effects.slots[2].signature.action.contraction_count);
}

test "projector constructor contracts structural primitives by signature table" {
    const testing = std.testing;

    var first: ProjectorCandidateWord = .{};
    try first.append(.{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(1, 3),
        .output_block = tensorFormRankBlock(3, 2),
        .auxiliary_block = tensorFormRankBlock(3, 4),
        .rank = 3,
        .output_rank = 2,
        .auxiliary_rank = 4,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });

    var same_signature: ProjectorCandidateWord = .{};
    try same_signature.append(.{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(7, 3),
        .output_block = tensorFormRankBlock(9, 2),
        .auxiliary_block = tensorFormRankBlock(9, 4),
        .rank = 3,
        .output_rank = 2,
        .auxiliary_rank = 4,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });

    try testing.expect(!projectorCandidateWordEql(first, same_signature));
    const off_diagonal = try structuralCandidateInnerProduct(first, same_signature);
    try testing.expectEqual(@as(i64, 1), off_diagonal.numerator);
    try testing.expectEqual(@as(i64, 1), off_diagonal.denominator);

    var rank_mismatch: ProjectorCandidateWord = .{};
    try rank_mismatch.append(.{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(7, 4),
        .output_block = tensorFormRankBlock(9, 3),
        .auxiliary_block = tensorFormRankBlock(9, 5),
        .rank = 4,
        .output_rank = 3,
        .auxiliary_rank = 5,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });
    const orthogonal = try structuralCandidateInnerProduct(first, rank_mismatch);
    try testing.expectEqual(@as(i64, 0), orthogonal.numerator);

    var unsupported: ProjectorCandidateWord = .{};
    try unsupported.append(.{
        .kind = .spinor_tower_contract,
        .input_block = 1,
        .output_block = 2,
        .rank = 2,
        .output_rank = 1,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });
    try testing.expectError(error.UnsupportedContraction, structuralCandidateInnerProduct(first, unsupported));

    var candidates: ProjectorCandidateBuffer = .{};
    try candidates.append(first);
    try candidates.append(same_signature);
    const program = try compileProjectorProgram(candidates, .{ .inner_product = structuralFixtureInnerProduct });
    try testing.expectEqual(@as(u8, 1), program.pivot_count);
    try testing.expectEqual(@as(u8, 0), program.pivots[0]);
}

test "projector constructor obtains nontrivial exterior-gamma Gram coefficients" {
    const testing = std.testing;

    var left: ProjectorCandidateWord = .{};
    try left.append(.{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(1, 3),
        .output_block = tensorFormRankBlock(3, 2),
        .auxiliary_block = tensorFormRankBlock(3, 4),
        .rank = 3,
        .output_rank = 2,
        .auxiliary_rank = 4,
        .action_gamma_rank = 3,
        .action_contraction_count = 2,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });

    var right: ProjectorCandidateWord = .{};
    try right.append(.{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(7, 3),
        .output_block = tensorFormRankBlock(9, 2),
        .auxiliary_block = tensorFormRankBlock(9, 4),
        .rank = 3,
        .output_rank = 2,
        .auxiliary_rank = 4,
        .action_gamma_rank = 3,
        .action_contraction_count = 2,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });

    const value = try structuralCandidateInnerProduct(left, right);
    try testing.expectEqual(@as(i64, -18), value.numerator);
    try testing.expectEqual(@as(i64, 1), value.denominator);
}

test "projector constructor obtains form-delta Gram binomial coefficients" {
    const testing = std.testing;

    var left: ProjectorCandidateWord = .{};
    try left.append(.{
        .kind = .form_delta,
        .input_block = tensorFormRankBlock(1, 3),
        .output_block = tensorFormRankBlock(3, 3),
        .rank = 3,
        .orthogonal_dimension = 10,
    });

    var right: ProjectorCandidateWord = .{};
    try right.append(.{
        .kind = .form_delta,
        .input_block = tensorFormRankBlock(7, 3),
        .output_block = tensorFormRankBlock(9, 3),
        .rank = 3,
        .orthogonal_dimension = 10,
    });

    const value = try structuralCandidateInnerProduct(left, right);
    try testing.expectEqual(@as(i64, 120), value.numerator);
    try testing.expectEqual(@as(i64, 1), value.denominator);

    var mismatch: ProjectorCandidateWord = .{};
    try mismatch.append(.{
        .kind = .form_delta,
        .input_block = tensorFormRankBlock(7, 4),
        .output_block = tensorFormRankBlock(9, 4),
        .rank = 4,
        .orthogonal_dimension = 10,
    });
    const orthogonal = try structuralCandidateInnerProduct(left, mismatch);
    try testing.expectEqual(@as(i64, 0), orthogonal.numerator);
}

test "projector constructor obtains spinor-tower Gram coefficients" {
    const testing = std.testing;

    var lowering: ProjectorCandidateWord = .{};
    try lowering.append(.{
        .kind = .spinor_tower_contract,
        .rank = 4,
        .output_rank = 3,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });
    const lowering_norm = try structuralCandidateInnerProduct(lowering, lowering);
    try testing.expectEqual(@as(i64, 4), lowering_norm.numerator);
    try testing.expectEqual(@as(i64, 1), lowering_norm.denominator);

    var raising: ProjectorCandidateWord = .{};
    try raising.append(.{
        .kind = .spinor_tower_contract_adjoint,
        .rank = 3,
        .output_rank = 4,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });
    const raising_norm = try structuralCandidateInnerProduct(raising, raising);
    try testing.expectEqual(@as(i64, 19), raising_norm.numerator);
    try testing.expectEqual(@as(i64, 1), raising_norm.denominator);

    var form_raising: ProjectorCandidateWord = .{};
    try form_raising.append(.{
        .kind = .spinor_tower_contract_adjoint,
        .rank = 0,
        .output_rank = 1,
        .auxiliary_rank = 2,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });
    const form_raising_norm = try structuralCandidateInnerProduct(form_raising, form_raising);
    try testing.expectEqual(@as(i64, 16), form_raising_norm.numerator);
    try testing.expectEqual(@as(i64, 1), form_raising_norm.denominator);
}

test "projector constructor contracts Hodge projectors with middle-rank gamma actions" {
    const testing = std.testing;

    var hodge: ProjectorCandidateWord = .{};
    try hodge.append(.{
        .kind = .hodge_project,
        .input_block = tensorFormRankBlock(1, 3),
        .output_block = tensorFormRankBlock(3, 5),
        .rank = 2,
        .output_rank = 5,
        .action_gamma_rank = 2,
        .action_contraction_count = 0,
        .orthogonal_dimension = 10,
        .chirality = 1,
        .duality = .self_dual,
    });

    var middle_gamma: ProjectorCandidateWord = .{};
    try middle_gamma.append(.{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(7, 3),
        .output_block = tensorFormRankBlock(9, 5),
        .rank = 3,
        .output_rank = 5,
        .action_gamma_rank = 2,
        .action_contraction_count = 0,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });

    const mixed = try structuralCandidateInnerProduct(hodge, middle_gamma);
    try testing.expectEqual(@as(i64, 1), mixed.numerator);
    try testing.expectEqual(@as(i64, 1), mixed.denominator);

    var lower_gamma: ProjectorCandidateWord = .{};
    try lower_gamma.append(.{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(7, 3),
        .output_block = tensorFormRankBlock(9, 4),
        .rank = 3,
        .output_rank = 4,
        .action_gamma_rank = 1,
        .action_contraction_count = 0,
        .orthogonal_dimension = 10,
        .chirality = 1,
    });
    const orthogonal = try structuralCandidateInnerProduct(hodge, lower_gamma);
    try testing.expectEqual(@as(i64, 0), orthogonal.numerator);
}

test "projector constructor contracts form deltas with exterior-gamma identities" {
    const testing = std.testing;

    var delta: ProjectorCandidateWord = .{};
    try delta.append(.{
        .kind = .form_delta,
        .input_block = tensorFormRankBlock(1, 3),
        .output_block = tensorFormRankBlock(3, 3),
        .rank = 3,
        .orthogonal_dimension = 10,
    });

    var gamma_identity: ProjectorCandidateWord = .{};
    try gamma_identity.append(.{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(7, 3),
        .output_block = tensorFormRankBlock(9, 3),
        .rank = 3,
        .output_rank = 3,
        .action_gamma_rank = 0,
        .action_contraction_count = 0,
        .orthogonal_dimension = 10,
    });

    const forward = try structuralCandidateInnerProduct(delta, gamma_identity);
    try testing.expectEqual(@as(i64, 120), forward.numerator);
    try testing.expectEqual(@as(i64, 1), forward.denominator);
    const reverse = try structuralCandidateInnerProduct(gamma_identity, delta);
    try testing.expectEqual(@as(i64, 120), reverse.numerator);
    try testing.expectEqual(@as(i64, 1), reverse.denominator);

    var gamma_trace_action: ProjectorCandidateWord = .{};
    try gamma_trace_action.append(.{
        .kind = .gamma_rank_split,
        .input_block = tensorFormRankBlock(7, 3),
        .output_block = tensorFormRankBlock(9, 3),
        .rank = 3,
        .output_rank = 3,
        .action_gamma_rank = 2,
        .action_contraction_count = 1,
        .orthogonal_dimension = 10,
    });
    const orthogonal = try structuralCandidateInnerProduct(delta, gamma_trace_action);
    try testing.expectEqual(@as(i64, 0), orthogonal.numerator);
}

test "projector constructor inverts a two-generator Gram matrix exactly" {
    const testing = std.testing;

    const inverse = try invertGram2(2, 1, 2);
    try testing.expectEqual(@as(i64, 2), inverse.at(0, 0).numerator);
    try testing.expectEqual(@as(i64, 3), inverse.at(0, 0).denominator);
    try testing.expectEqual(@as(i64, -1), inverse.at(0, 1).numerator);
    try testing.expectEqual(@as(i64, 3), inverse.at(0, 1).denominator);
    try testing.expectEqual(@as(i64, -1), inverse.at(1, 0).numerator);
    try testing.expectEqual(@as(i64, 3), inverse.at(1, 0).denominator);
    try testing.expectEqual(@as(i64, 2), inverse.at(1, 1).numerator);
    try testing.expectEqual(@as(i64, 3), inverse.at(1, 1).denominator);

    try testing.expectError(error.SingularGramMatrix, invertGram2(1, 1, 1));
}

test "projector constructor selects independent Gram pivots" {
    const testing = std.testing;

    const rank_one = [_]Rational{
        try Rational.init(1, 1), try Rational.init(1, 1),
        try Rational.init(1, 1), try Rational.init(1, 1),
    };
    const rank_one_pivots = try selectIndependentGramPivots(2, rank_one[0..]);
    try testing.expectEqual(@as(u8, 1), rank_one_pivots.count);
    try testing.expectEqual(@as(u8, 0), rank_one_pivots.pivots[0]);

    const shifted = [_]Rational{
        Rational.zero(), Rational.zero(),         Rational.zero(),
        Rational.zero(), try Rational.init(2, 1), Rational.zero(),
        Rational.zero(), Rational.zero(),         try Rational.init(3, 1),
    };
    const shifted_pivots = try selectIndependentGramPivots(3, shifted[0..]);
    try testing.expectEqual(@as(u8, 2), shifted_pivots.count);
    try testing.expectEqual(@as(u8, 1), shifted_pivots.pivots[0]);
    try testing.expectEqual(@as(u8, 2), shifted_pivots.pivots[1]);
}

test "projector constructor inverts a small exact Gram matrix" {
    const testing = std.testing;

    const entries = [_]Rational{
        try Rational.init(2, 1), try Rational.init(1, 1), try Rational.init(0, 1),
        try Rational.init(1, 1), try Rational.init(2, 1), try Rational.init(0, 1),
        try Rational.init(0, 1), try Rational.init(0, 1), try Rational.init(4, 1),
    };
    const inverse = try invertSmallGram(3, entries[0..]);
    try testing.expectEqual(@as(i64, 2), inverse[0].numerator);
    try testing.expectEqual(@as(i64, 3), inverse[0].denominator);
    try testing.expectEqual(@as(i64, -1), inverse[1].numerator);
    try testing.expectEqual(@as(i64, 3), inverse[1].denominator);
    try testing.expectEqual(@as(i64, 1), inverse[8].numerator);
    try testing.expectEqual(@as(i64, 4), inverse[8].denominator);
}

test "projector constructor streams dense generic programs past u8 term index" {
    const testing = std.testing;

    var program: ProjectorProgram = .{ .candidate_count = max_program_pivots, .pivot_count = max_program_pivots };
    var pivot_index: u8 = 0;
    while (pivot_index < max_program_pivots) : (pivot_index += 1) {
        program.pivots[pivot_index] = pivot_index;
    }
    var entry_index: usize = 0;
    while (entry_index < max_program_gram_entries) : (entry_index += 1) {
        program.inverse_gram[entry_index] = Rational.one();
    }

    try testing.expectEqual(@as(u16, 1024), projectorProgramTermCount(program));
    const last = try projectorProgramTermAt(program, 1023);
    try testing.expectEqual(@as(u8, 31), last.left_candidate);
    try testing.expectEqual(@as(u8, 31), last.right_candidate);
    try testing.expectEqual(@as(i64, 1), last.coefficient.numerator);
    try testing.expectError(error.ProjectorConstructorTermOutOfBounds, projectorProgramTermAt(program, 1024));
}

test "projector constructor reports typed pivot cap for generic programs" {
    const testing = std.testing;

    var candidates: ProjectorCandidateBuffer = .{};
    var candidate_index: u8 = 0;
    while (candidate_index <= max_program_pivots) : (candidate_index += 1) {
        var word: ProjectorCandidateWord = .{};
        try word.append(.{
            .kind = .form_delta,
            .input_block = candidate_index,
            .output_block = candidate_index,
        });
        try candidates.append(word);
    }
    try testing.expectError(error.UnsupportedTensorPivotCap, compileProjectorProgram(candidates, .{ .inner_product = pivotCapFixtureInnerProduct }));
}

test "projector constructor compiles a channel through backend callbacks" {
    const testing = std.testing;

    const spec: TensorFormProjectionSpec = .{
        .operator_id = 5,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = 0,
        .input_form_mask = 0,
        .output_form_profile = 0,
        .output_form_count = 0,
        .output_form_rank = 0,
        .chirality = 0,
    };
    const program = try compileProjectorProgramForChannel(.{ .tensor_form_projection = spec }, .{
        .enumerate_candidates = backendFixtureEnumerateCandidates,
        .inner_product = backendFixtureInnerProduct,
    });

    try testing.expectEqual(@as(u8, 1), program.candidate_count);
    try testing.expectEqual(@as(u8, 1), program.pivot_count);
    try testing.expectEqual(ProjectorPrimitiveKind.form_delta, program.candidates[0].slots[0].kind);
    try testing.expectEqual(@as(i64, 1), program.inverse_gram[0].numerator);
    try testing.expectEqual(@as(i64, 2), program.inverse_gram[0].denominator);
}

test "projector constructor compiles rank-split candidates through Gram pivots" {
    const testing = std.testing;

    const spec: TensorFormProjectionSpec = .{
        .operator_id = 41,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 8),
        .input_form_mask = 0b101,
        .output_form_profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4) | (@as(u128, 1) << 12),
        .output_form_count = 3,
        .output_form_rank = 1,
        .chirality = 1,
    };
    const program = try compileStructuralProjectorProgram(structuralProjectorSpecFromTensorForm(spec));
    try testing.expectEqual(@as(u8, 1), program.candidate_count);
    try testing.expectEqual(@as(u8, 1), program.pivot_count);
    try testing.expectEqual(@as(u8, 0), program.pivots[0]);
    try testing.expectEqual(@as(i64, 1), program.inverse_gram[0].numerator);
    try testing.expectEqual(@as(i64, 10), program.inverse_gram[0].denominator);
    try testing.expectEqual(@as(u8, 2), program.candidates[0].count);
    try testing.expectEqual(ProjectorPrimitiveKind.gamma_rank_split, program.candidates[0].slots[0].kind);
    try testing.expectEqual(ProjectorPrimitiveKind.form_delta, program.candidates[0].slots[1].kind);
}

test "projector constructor removes dependent candidates by exact Gram" {
    const testing = std.testing;

    var first: ProjectorCandidateWord = .{};
    try first.append(.{
        .kind = .form_delta,
        .input_block = 1,
        .output_block = 2,
    });
    var second: ProjectorCandidateWord = .{};
    try second.append(.{
        .kind = .form_delta,
        .input_block = 3,
        .output_block = 4,
    });

    var candidates: ProjectorCandidateBuffer = .{};
    try candidates.append(first);
    try candidates.append(second);

    const program = try compileProjectorProgram(candidates, .{ .inner_product = dependentCandidateFixtureInnerProduct });
    try testing.expectEqual(@as(u8, 2), program.candidate_count);
    try testing.expectEqual(@as(u8, 1), program.pivot_count);
    try testing.expectEqual(@as(u8, 0), program.pivots[0]);
    try testing.expectEqual(@as(u16, 1), projectorProgramTermCount(program));

    const term = try projectorProgramTermAt(program, 0);
    try testing.expectEqual(@as(u8, 0), term.left_candidate);
    try testing.expectEqual(@as(u8, 0), term.right_candidate);
    try testing.expectEqual(@as(i64, 1), term.coefficient.numerator);
    try testing.expectEqual(@as(i64, 1), term.coefficient.denominator);
}

test "projector constructor streams off-diagonal inverse Gram terms" {
    const testing = std.testing;

    var first: ProjectorCandidateWord = .{};
    try first.append(.{
        .kind = .form_delta,
        .rank = 1,
    });
    var second: ProjectorCandidateWord = .{};
    try second.append(.{
        .kind = .form_delta,
        .rank = 2,
    });

    var candidates: ProjectorCandidateBuffer = .{};
    try candidates.append(first);
    try candidates.append(second);

    const program = try compileProjectorProgram(candidates, .{ .inner_product = offDiagonalFixtureInnerProduct });
    try testing.expectEqual(@as(u8, 2), program.pivot_count);
    try testing.expectEqual(@as(u16, 4), projectorProgramTermCount(program));

    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            var entry = Rational.zero();
            var mid: u8 = 0;
            while (mid < program.pivot_count) : (mid += 1) {
                const gram_entry = try offDiagonalFixtureInnerProduct(null, program.candidates[program.pivots[row]], program.candidates[program.pivots[mid]]);
                const inverse_entry = program.inverse_gram[@as(usize, mid) * program.pivot_count + column];
                entry = try entry.add(try gram_entry.mul(inverse_entry));
            }
            try testing.expectEqual(if (row == column) @as(i64, 1) else @as(i64, 0), entry.numerator);
            try testing.expectEqual(@as(i64, 1), entry.denominator);
        }
    }

    const off_diagonal = try projectorProgramTermAt(program, 1);
    try testing.expectEqual(@as(u8, 0), off_diagonal.left_candidate);
    try testing.expectEqual(@as(u8, 1), off_diagonal.right_candidate);
    try testing.expectEqual(@as(i64, -1), off_diagonal.coefficient.numerator);
    try testing.expectEqual(@as(i64, 3), off_diagonal.coefficient.denominator);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    const coefficient = try appendProjectorProgramTermAtoms(testing.allocator, &atoms, .{
        .operator_id = 17,
        .left = 10,
        .right = 11,
        .output = 12,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 0,
        .input_form_mask = 1,
        .output_form_profile = @as(u128, 1) << 0,
        .output_form_count = 1,
        .output_form_rank = 1,
        .chirality = 1,
    }, program, 1);
    try testing.expectEqual(@as(i32, -1), rendering.rationalValue(coefficient).numerator);
    try testing.expectEqual(@as(u32, 3), rendering.rationalValue(coefficient).denominator);
    try testing.expect(atoms.items.len >= 2);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).generalized_delta, std.meta.activeTag(atoms.items[0]));
    try testing.expectEqual(tensorFormCarriedBlock(10), atoms.items[0].generalized_delta.upper);
    try testing.expectEqual(tensorFormCarriedBlock(12), atoms.items[0].generalized_delta.lower);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).generalized_delta, std.meta.activeTag(atoms.items[1]));
    try testing.expectEqual(tensorFormCarriedBlock(12), atoms.items[1].generalized_delta.upper);
    try testing.expectEqual(tensorFormCarriedBlock(10), atoms.items[1].generalized_delta.lower);
}

test "projector constructor compiles vector-spinor trace subtraction through Gram" {
    const testing = std.testing;

    const spec: VectorSpinorTracelessSpec = .{
        .operator_id = 11,
        .vector = 2,
        .spinor = 3,
        .orthogonal_dimension = 10,
        .chirality = 2,
    };

    const program = try compileVectorSpinorTracelessProgram(spec);
    try testing.expectEqual(@as(u8, 2), program.candidate_count);
    try testing.expectEqual(@as(u8, 2), program.pivot_count);
    try testing.expectEqual(ProjectorPrimitiveKind.vector_spinor_identity, program.candidates[0].slots[0].kind);
    try testing.expectEqual(ProjectorPrimitiveKind.gamma_trace, program.candidates[1].slots[0].kind);
    try testing.expectEqual(@as(u16, 2), projectorProgramTermCount(program));

    const identity = try projectorProgramTermAt(program, 0);
    try testing.expectEqual(@as(u8, 0), identity.left_candidate);
    try testing.expectEqual(@as(i64, 1), identity.coefficient.numerator);
    try testing.expectEqual(@as(i64, 1), identity.coefficient.denominator);

    const trace = try projectorProgramTermAt(program, 1);
    try testing.expectEqual(@as(u8, 1), trace.left_candidate);
    try testing.expectEqual(@as(i64, -1), trace.coefficient.numerator);
    try testing.expectEqual(@as(i64, 10), trace.coefficient.denominator);
}

test "projector constructor compiles middle-form dual projection through Gram" {
    const testing = std.testing;

    const spec: TensorFormProjectionSpec = .{
        .operator_id = 43,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_mask = 0b100,
        .output_form_profile = 0,
        .output_form_count = 1,
        .output_form_rank = 5,
        .output_duality = .anti_self_dual,
        .chirality = 2,
    };

    const program = try compileStructuralProjectorProgram(structuralProjectorSpecFromTensorForm(spec));
    try testing.expectEqual(@as(u8, 1), program.candidate_count);
    try testing.expectEqual(@as(u8, 1), program.pivot_count);
    try testing.expectEqual(ProjectorPrimitiveKind.hodge_project, program.candidates[0].slots[0].kind);
    try testing.expectEqual(@as(u8, 2), program.candidates[0].slots[0].rank);
    try testing.expectEqual(rendering.DualityTag.anti_self_dual, program.candidates[0].slots[0].duality);
    try testing.expectEqual(@as(u16, 1), projectorProgramTermCount(program));

    const term = try projectorProgramTermAt(program, 0);
    try testing.expectEqual(@as(u8, 0), term.left_candidate);
    try testing.expectEqual(@as(i64, 1), term.coefficient.numerator);
    try testing.expectEqual(@as(i64, 1), term.coefficient.denominator);
}

test "projector constructor emits primitive terminal gamma expression" {
    const testing = std.testing;

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);

    try appendTensorFormGammaExpression(testing.allocator, &atoms, .{
        .operator_id = 7,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 0,
        .output_form_profile = @as(u128, 1) << 8,
        .chirality = 1,
    });

    try testing.expectEqual(@as(usize, 2), atoms.items.len);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).gamma_form, std.meta.activeTag(atoms.items[0]));
    try testing.expectEqual(@as(u8, 2), atoms.items[0].gamma_form.rank);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).generalized_delta, std.meta.activeTag(atoms.items[1]));
}

test "projector constructor bulk-lowers supported tensor-form projections" {
    const testing = std.testing;

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);

    const lowered = try appendTensorFormProjectionExpression(testing.allocator, &atoms, .{
        .operator_id = 13,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_mask = 0b100,
        .output_form_profile = (@as(u128, 1) << 8) | (@as(u128, 1) << 0),
        .output_form_count = 2,
        .output_form_rank = 1,
        .chirality = 1,
    });
    try testing.expect(lowered);
    try testing.expectEqual(@as(usize, 4), atoms.items.len);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).gamma_form, std.meta.activeTag(atoms.items[0]));
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).generalized_delta, std.meta.activeTag(atoms.items[1]));
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).generalized_delta, std.meta.activeTag(atoms.items[2]));
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).gamma_action, std.meta.activeTag(atoms.items[3]));
}

test "projector constructor compiles gamma-delta tensor-form projection through Gram" {
    const testing = std.testing;

    const spec: TensorFormProjectionSpec = .{
        .operator_id = 13,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_mask = 0b100,
        .output_form_profile = (@as(u128, 1) << 8) | (@as(u128, 1) << 0),
        .output_form_count = 2,
        .output_form_rank = 1,
        .chirality = 1,
    };
    const program = try compileStructuralProjectorProgram(structuralProjectorSpecFromTensorForm(spec));
    try testing.expectEqual(@as(u8, 1), program.candidate_count);
    try testing.expectEqual(@as(u8, 1), program.pivot_count);
    try testing.expectEqual(@as(u8, 2), program.candidates[0].count);
    try testing.expectEqual(ProjectorPrimitiveKind.gamma_insert, program.candidates[0].slots[0].kind);
    try testing.expectEqual(@as(u8, 1), program.candidates[0].slots[0].rank);
    try testing.expectEqual(tensorFormInsertedBlock(spec.output, 1), program.candidates[0].slots[0].output_block);
    try testing.expectEqual(ProjectorPrimitiveKind.form_delta, program.candidates[0].slots[1].kind);
    try testing.expectEqual(@as(u16, 1), projectorProgramTermCount(program));

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    const coefficient = try appendTensorFormProjectionTerm(testing.allocator, &atoms, spec, 0);
    try testing.expectEqual(rendering.rationalOne(), coefficient);
    try testing.expectEqual(@as(usize, 4), atoms.items.len);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).gamma_form, std.meta.activeTag(atoms.items[0]));
    try testing.expectEqual(@as(u8, 1), atoms.items[0].gamma_form.rank);
    try testing.expectEqual(tensorSpinorSpinorIndex(spec.left), atoms.items[0].gamma_form.spinor_left);
    try testing.expectEqual(spec.right, atoms.items[0].gamma_form.spinor_right);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).generalized_delta, std.meta.activeTag(atoms.items[1]));
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).generalized_delta, std.meta.activeTag(atoms.items[2]));
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).gamma_action, std.meta.activeTag(atoms.items[3]));
    try testing.expectEqual(@as(u8, 1), atoms.items[3].gamma_action.rank);
    try testing.expectEqual(spec.right, atoms.items[3].gamma_action.spinor_input);
    try testing.expectEqual(tensorSpinorSpinorIndex(spec.left), atoms.items[3].gamma_action.spinor_output);
}

test "projector constructor classifies tensor-form projection transitions" {
    const testing = std.testing;

    const gamma_delta: TensorFormProjectionSpec = .{
        .operator_id = 13,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_mask = 0b100,
        .output_form_profile = (@as(u128, 1) << 8) | (@as(u128, 1) << 0),
        .output_form_count = 2,
        .output_form_rank = 1,
        .chirality = 1,
    };
    try testing.expectEqual(TensorFormProjectionTransition.gamma_delta, tensorFormProjectionTransition(gamma_delta));
    try testing.expectEqual(@as(u16, 1), tensorFormProjectionTermCount(gamma_delta));

    const rank_split: TensorFormProjectionSpec = .{
        .operator_id = 19,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_mask = 0b100,
        .output_form_profile = (@as(u128, 1) << 4) | (@as(u128, 1) << 12),
        .output_form_count = 2,
        .output_form_rank = 2,
        .chirality = 1,
    };
    try testing.expectEqual(TensorFormProjectionTransition.rank_split, tensorFormProjectionTransition(rank_split));
    try testing.expectEqual(@as(u16, 1), tensorFormProjectionTermCount(rank_split));

    const middle_dual: TensorFormProjectionSpec = .{
        .operator_id = 23,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_mask = 0b100,
        .output_form_profile = 0,
        .output_form_count = 1,
        .output_form_rank = 5,
        .output_duality = .anti_self_dual,
        .chirality = 2,
    };
    try testing.expectEqual(TensorFormProjectionTransition.middle_dual, tensorFormProjectionTransition(middle_dual));
    try testing.expectEqual(@as(u16, 1), tensorFormProjectionTermCount(middle_dual));
}

test "projector constructor classifies profile transforms for structural candidates" {
    const testing = std.testing;

    const rank1 = @as(u128, 1) << 0;
    const rank2 = @as(u128, 1) << 4;
    const rank3 = @as(u128, 1) << 8;
    const rank4 = @as(u128, 1) << 12;

    const preserved = classifyProfileTransform(rank3, rank3);
    try testing.expectEqual(ProfileTransformKind.preserve, preserved.kind);

    const added = classifyProfileTransform(rank3, rank3 | rank1);
    try testing.expectEqual(ProfileTransformKind.add_rank, added.kind);
    try testing.expectEqual(@as(u8, 1), added.rank);

    const shifted = classifyProfileTransform(rank1 | rank3, rank2 | rank4);
    try testing.expectEqual(ProfileTransformKind.shift_all_up, shifted.kind);
    try testing.expectEqual(@as(u8, 1), shifted.source_rank);
    try testing.expectEqual(@as(u8, 2), shifted.target_rank);

    const moved = classifyProfileTransform(rank1 | rank4, rank2 | rank4);
    try testing.expectEqual(ProfileTransformKind.move_rank_up, moved.kind);
    try testing.expectEqual(@as(u8, 1), moved.source_rank);
    try testing.expectEqual(@as(u8, 2), moved.target_rank);

    const split = classifyProfileTransform(rank3, rank2 | rank4);
    try testing.expectEqual(ProfileTransformKind.split_rank, split.kind);
    try testing.expectEqual(@as(u8, 3), split.source_rank);
    try testing.expectEqual(@as(u8, 2), split.lower_rank);
    try testing.expectEqual(@as(u8, 4), split.upper_rank);

    const removed = classifyProfileTransform(rank1 | rank3, rank3);
    try testing.expectEqual(ProfileTransformKind.remove_rank, removed.kind);
    try testing.expectEqual(@as(u8, 1), removed.rank);
}

test "projector constructor audits structural coverage by profile transform" {
    const testing = std.testing;

    var audit: StructuralProjectorCoverageAudit = .{};
    audit.recordTensorSpinorProjection(.{
        .operator_id = 31,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_count = 1,
        .input_tower_power = 4,
        .form_rank = 3,
        .form_count = 1,
        .form_mask = 0b100,
        .form_profile = @as(u128, 1) << 8,
        .tower_power = 3,
        .chirality = 1,
    });
    audit.recordTensorSpinorProjection(.{
        .operator_id = 32,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .left_has_spinor = false,
        .input_form_profile = @as(u128, 1) << 0,
        .input_form_count = 1,
        .input_tower_power = 4,
        .form_rank = 2,
        .form_count = 1,
        .form_mask = 0b10,
        .form_profile = @as(u128, 1) << 4,
        .tower_power = 6,
        .chirality = 1,
    });
    audit.recordTensorFormProjection(.{
        .operator_id = 33,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_mask = 0b100,
        .output_form_profile = (@as(u128, 1) << 4) | (@as(u128, 1) << 12),
        .output_form_count = 2,
        .output_form_rank = 2,
        .chirality = 1,
    });
    audit.recordTensorSpinorProjection(.{
        .operator_id = 34,
        .left = 4,
        .right = 5,
        .output = 6,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_count = 1,
        .input_tower_power = 4,
        .form_rank = 3,
        .form_count = 1,
        .form_mask = 0b100,
        .form_profile = @as(u128, 1) << 8,
        .tower_power = 3,
        .chirality = 1,
    });
    audit.recordTensorSpinorProjection(.{
        .operator_id = 35,
        .left = 7,
        .right = 8,
        .output = 9,
        .orthogonal_dimension = 10,
        .left_has_spinor = false,
        .input_form_profile = @as(u128, 1) << 0,
        .input_form_count = 1,
        .input_tower_power = 4,
        .form_rank = 2,
        .form_count = 1,
        .form_mask = 0b10,
        .form_profile = @as(u128, 1) << 4,
        .tower_power = 6,
        .chirality = 1,
    });

    try testing.expectEqual(@as(u64, 4), audit.tensor_spinor_projection_count);
    try testing.expectEqual(@as(u64, 2), audit.tensor_spinor_structural_count);
    try testing.expectEqual(@as(u64, 1), audit.tensor_form_projection_count);
    try testing.expectEqual(@as(u64, 1), audit.tensor_form_structural_count);
    try testing.expectEqual(@as(u64, 2), audit.preserve_count);
    try testing.expectEqual(@as(u64, 2), audit.shift_all_up_count);
    try testing.expectEqual(@as(u64, 1), audit.split_rank_count);
    try testing.expectEqual(@as(u64, 5), audit.structural_projection_count);
    try testing.expectEqual(@as(u64, 3), audit.structural_projection_solved_count);
    try testing.expectEqual(@as(u64, 2), audit.structural_projection_unsupported_count);
    try testing.expectEqual(@as(u64, 3), audit.distinct_structural_key_count);
    try testing.expectEqual(@as(u64, 2), audit.distinct_structural_solved_key_count);
    try testing.expectEqual(@as(u64, 1), audit.distinct_structural_unsupported_key_count);
    try testing.expectEqual(@as(u64, 0), audit.structural_key_overflow_count);
    try testing.expect(audit.largest_unsupported_key_hashes[0] != 0);
    try testing.expectEqual(@as(u64, 2), audit.largest_unsupported_key_counts[0]);
    try testing.expectEqual(@as(u16, 10), audit.largest_unsupported_key_summaries[0].dimension);
    try testing.expectEqual(@as(u128, 1) << 0, audit.largest_unsupported_key_summaries[0].source_form_profile);
    try testing.expectEqual(@as(u128, 1) << 4, audit.largest_unsupported_key_summaries[0].target_form_profile);
    try testing.expectEqual(@as(u16, 0), audit.largest_unsupported_key_summaries[0].source_tower_power);
    try testing.expectEqual(@as(u16, 6), audit.largest_unsupported_key_summaries[0].target_tower_power);
    try testing.expect(!audit.largest_unsupported_key_summaries[0].source_has_spinor);
    try testing.expect(audit.largest_unsupported_key_summaries[0].right_has_spinor);
    try testing.expect(audit.largest_unsupported_key_summaries[0].target_has_spinor);
    try testing.expectEqual(@as(u8, 1), audit.largest_unsupported_key_summaries[0].target_chirality);
}

test "projector constructor searches structural primitive effects by endpoint state" {
    const testing = std.testing;

    const lowering = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 41,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .tower_power = 4,
            .chirality = 1,
            .has_spinor = true,
        },
        .right = .{
            .index = 2,
            .chirality = 1,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .tower_power = 3,
            .chirality = 1,
            .has_spinor = true,
        },
    });
    try testing.expectEqual(@as(u8, 1), lowering.count);
    try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract, lowering.words[0].slots[0].kind);

    const raising = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 42,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = @as(u128, 1) << 8,
            .tower_power = 3,
            .chirality = 1,
            .has_spinor = true,
        },
        .right = .{
            .index = 2,
            .chirality = 1,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .form_profile = @as(u128, 1) << 8,
            .tower_power = 4,
            .chirality = 1,
            .has_spinor = true,
        },
    });
    try testing.expectEqual(@as(u8, 1), raising.count);
    try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract_adjoint, raising.words[0].slots[0].kind);
    try testing.expectEqual(ProjectorPrimitiveKind.form_delta, raising.words[0].slots[1].kind);

    const rank_split = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 43,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = @as(u128, 1) << 8,
            .chirality = 1,
            .has_spinor = true,
        },
        .right = .{
            .index = 2,
            .chirality = 1,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .form_profile = (@as(u128, 1) << 4) | (@as(u128, 1) << 12),
        },
    });
    try testing.expectEqual(@as(u8, 1), rank_split.count);
    try testing.expectEqual(ProjectorPrimitiveKind.gamma_rank_split, rank_split.words[0].slots[0].kind);

    const form_spinor = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 44,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = @as(u128, 2) << 4,
        },
        .right = .{
            .index = 2,
            .chirality = 1,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .form_profile = @as(u128, 1) << 4,
            .tower_power = 1,
            .chirality = 1,
            .has_spinor = true,
        },
    });
    try testing.expectEqual(@as(u8, 1), form_spinor.count);
    try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract_adjoint, form_spinor.words[0].slots[0].kind);
    try testing.expectEqual(tensorFormRankBlock(1, 2), form_spinor.words[0].slots[0].auxiliary_block);
    try testing.expectEqual(ProjectorPrimitiveKind.form_delta, form_spinor.words[0].slots[1].kind);
    try testing.expectEqual(tensorFormRankBlock(1, 2), form_spinor.words[0].slots[1].input_block);
    try testing.expectEqual(tensorFormRankBlock(3, 2), form_spinor.words[0].slots[1].output_block);

    const form_spinor_preserve = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 45,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = @as(u128, 1) << 4,
        },
        .right = .{
            .index = 2,
            .chirality = 1,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .form_profile = @as(u128, 1) << 4,
            .tower_power = 1,
            .chirality = 1,
            .has_spinor = true,
        },
    });
    try testing.expectEqual(@as(u8, 1), form_spinor_preserve.count);
    try testing.expectEqual(@as(u8, 2), form_spinor_preserve.words[0].count);
    try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract_adjoint, form_spinor_preserve.words[0].slots[0].kind);
    try testing.expectEqual(@as(u8, 0), form_spinor_preserve.words[0].slots[0].auxiliary_rank);
    try testing.expectEqual(@as(rendering.IndexBlockId, 0), form_spinor_preserve.words[0].slots[0].auxiliary_block);
    try testing.expectEqual(ProjectorPrimitiveKind.form_delta, form_spinor_preserve.words[0].slots[1].kind);
}

test "projector constructor composes generated structural moves" {
    const testing = std.testing;

    const rank2 = @as(u128, 1) << 4;
    const rank4 = @as(u128, 1) << 12;
    const words = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 47,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .tower_power = 4,
            .chirality = 1,
            .has_spinor = true,
        },
        .right = .{
            .index = 2,
            .chirality = 1,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .form_profile = rank2 | rank4,
            .tower_power = 2,
            .chirality = 1,
            .has_spinor = true,
        },
    });

    try testing.expectEqual(@as(u8, 2), words.count);
    var word_index: u8 = 0;
    while (word_index < words.count) : (word_index += 1) {
        try testing.expectEqual(@as(u8, 2), words.words[word_index].count);
        try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract, words.words[word_index].slots[0].kind);
        try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract, words.words[word_index].slots[1].kind);
        try testing.expect(words.words[word_index].slots[0].auxiliary_rank != words.words[word_index].slots[1].auxiliary_rank);
    }
}

test "projector constructor generates tensor-spinor form consumption moves" {
    const testing = std.testing;

    const rank1 = @as(u128, 1) << 0;
    const rank3 = @as(u128, 1) << 8;
    const rank4 = @as(u128, 1) << 12;

    const even_rank = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 48,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = rank1 | rank4,
            .tower_power = 2,
            .chirality = 2,
            .has_spinor = true,
        },
        .right = .{
            .index = 2,
            .chirality = 2,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .form_profile = rank1,
            .tower_power = 3,
            .chirality = 2,
            .has_spinor = true,
        },
    });
    try testing.expectEqual(@as(u8, 1), even_rank.count);
    try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract_adjoint, even_rank.words[0].slots[0].kind);
    try testing.expectEqual(@as(u8, 4), even_rank.words[0].slots[0].auxiliary_rank);
    try testing.expectEqual(tensorFormRankBlock(1, 4), even_rank.words[0].slots[0].auxiliary_block);
    try testing.expectEqual(ProjectorPrimitiveKind.form_delta, even_rank.words[0].slots[1].kind);

    const odd_rank_opposite = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 49,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = rank3,
            .tower_power = 2,
            .chirality = 2,
            .has_spinor = true,
        },
        .right = .{
            .index = 2,
            .chirality = 1,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .tower_power = 3,
            .chirality = 2,
            .has_spinor = true,
        },
    });
    try testing.expectEqual(@as(u8, 1), odd_rank_opposite.count);
    try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract_adjoint, odd_rank_opposite.words[0].slots[0].kind);
    try testing.expectEqual(@as(u8, 3), odd_rank_opposite.words[0].slots[0].auxiliary_rank);
    try testing.expectEqual(tensorFormRankBlock(1, 3), odd_rank_opposite.words[0].slots[0].auxiliary_block);
}

test "projector constructor generates opposite-chirality tower contractions" {
    const testing = std.testing;

    const rank3 = @as(u128, 1) << 8;
    const words = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 50,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = rank3,
            .tower_power = 3,
            .chirality = 1,
            .has_spinor = true,
        },
        .right = .{
            .index = 2,
            .chirality = 2,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .form_profile = rank3,
            .tower_power = 2,
            .chirality = 1,
            .has_spinor = true,
        },
    });

    try testing.expectEqual(@as(u8, 1), words.count);
    try testing.expectEqual(@as(u8, 2), words.words[0].count);
    try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract, words.words[0].slots[0].kind);
    try testing.expectEqual(@as(u8, 0), words.words[0].slots[0].auxiliary_rank);
    try testing.expectEqual(@as(rendering.IndexBlockId, 0), words.words[0].slots[0].auxiliary_block);
    try testing.expectEqual(ProjectorPrimitiveKind.form_delta, words.words[0].slots[1].kind);
    try testing.expectEqual(tensorFormRankBlock(1, 3), words.words[0].slots[1].input_block);
    try testing.expectEqual(tensorFormRankBlock(3, 3), words.words[0].slots[1].output_block);
}

test "projector constructor accepts both right chiralities for generated rank additions" {
    const testing = std.testing;

    const rank3 = @as(u128, 1) << 8;
    const opposite = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 51,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .tower_power = 4,
            .chirality = 2,
            .has_spinor = true,
        },
        .right = .{
            .index = 2,
            .chirality = 1,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .form_profile = rank3,
            .tower_power = 3,
            .chirality = 2,
            .has_spinor = true,
        },
    });
    try testing.expectEqual(@as(u8, 1), opposite.count);
    try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract, opposite.words[0].slots[0].kind);
    try testing.expectEqual(@as(u8, 3), opposite.words[0].slots[0].auxiliary_rank);

    const same = try enumerateOrthogonalStructuralCandidateWords(.{
        .operator_id = 52,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .tower_power = 4,
            .chirality = 2,
            .has_spinor = true,
        },
        .right = .{
            .index = 2,
            .chirality = 2,
            .has_spinor = true,
        },
        .output = .{
            .index = 3,
            .form_profile = rank3,
            .tower_power = 3,
            .chirality = 2,
            .has_spinor = true,
        },
    });
    try testing.expectEqual(@as(u8, 1), same.count);
    try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract, same.words[0].slots[0].kind);
    try testing.expectEqual(@as(u8, 3), same.words[0].slots[0].auxiliary_rank);
}

test "projector constructor generates structural primitive effects from endpoint states" {
    const testing = std.testing;

    const lowering = try generateOrthogonalStructuralPrimitiveEffects(.{
        .operator_id = 51,
        .orthogonal_dimension = 10,
        .left = .{ .index = 1, .has_spinor = true, .chirality = 1 },
        .right = .{ .index = 2, .has_spinor = true, .chirality = 1 },
        .output = .{ .index = 3, .has_spinor = true, .chirality = 1 },
    }, .{
        .form_profile = @as(u128, 1) << 8,
        .tower_power = 4,
        .has_spinor = true,
    }, .{
        .form_profile = (@as(u128, 1) << 8) | (@as(u128, 1) << 4),
        .tower_power = 3,
        .has_spinor = true,
    });
    try testing.expectEqual(@as(u8, 1), lowering.count);
    try testing.expectEqual(StructuralPrimitiveEffectKind.spinor_tower_contract, lowering.slots[0].kind);

    const form_spinor = try generateOrthogonalStructuralPrimitiveEffects(.{
        .operator_id = 52,
        .orthogonal_dimension = 10,
        .left = .{ .index = 1 },
        .right = .{ .index = 2, .has_spinor = true, .chirality = 2 },
        .output = .{ .index = 3, .has_spinor = true, .chirality = 1 },
    }, .{
        .form_profile = @as(u128, 1) << 8,
    }, .{
        .tower_power = 1,
        .has_spinor = true,
    });
    try testing.expectEqual(@as(u8, 1), form_spinor.count);
    try testing.expectEqual(StructuralPrimitiveEffectKind.form_spinor_contract_adjoint, form_spinor.slots[0].kind);

    const chirality_blocked = try generateOrthogonalStructuralPrimitiveEffects(.{
        .operator_id = 53,
        .orthogonal_dimension = 10,
        .left = .{ .index = 1 },
        .right = .{ .index = 2, .has_spinor = true, .chirality = 1 },
        .output = .{ .index = 3, .has_spinor = true, .chirality = 1 },
    }, .{
        .form_profile = @as(u128, 1) << 8,
    }, .{
        .tower_power = 1,
        .has_spinor = true,
    });
    try testing.expectEqual(@as(u8, 0), chirality_blocked.count);

    const gamma_insert = try generateOrthogonalStructuralPrimitiveEffects(.{
        .operator_id = 54,
        .orthogonal_dimension = 10,
        .left = .{ .index = 1, .has_spinor = true, .chirality = 1 },
        .right = .{ .index = 2, .has_spinor = true, .chirality = 2 },
        .output = .{ .index = 3 },
    }, .{
        .has_spinor = true,
        .chirality = 1,
    }, .{
        .form_profile = @as(u128, 1) << 4,
    });
    try testing.expectEqual(@as(u8, 1), gamma_insert.count);
    try testing.expectEqual(StructuralPrimitiveEffectKind.gamma_insert, gamma_insert.slots[0].kind);
    try testing.expectEqual(ProjectorPrimitiveKind.gamma_insert, gamma_insert.slots[0].signature.kind);
    try testing.expectEqual(@as(u8, 2), gamma_insert.slots[0].signature.action.gamma_rank);
    try testing.expectEqual(@as(u8, 2), gamma_insert.slots[0].signature.action.output_rank);

    const hodge = try generateOrthogonalStructuralPrimitiveEffects(.{
        .operator_id = 55,
        .orthogonal_dimension = 10,
        .left = .{ .index = 1, .has_spinor = true, .chirality = 1 },
        .right = .{ .index = 2, .has_spinor = true, .chirality = 2 },
        .output = .{ .index = 3, .form_count = 1, .form_rank = 5, .form_duality = .self_dual },
    }, .{
        .form_profile = @as(u128, 1) << 8,
        .has_spinor = true,
        .chirality = 1,
    }, .{});
    try testing.expectEqual(@as(u8, 1), hodge.count);
    try testing.expectEqual(StructuralPrimitiveEffectKind.hodge_project, hodge.slots[0].kind);
    try testing.expectEqual(ProjectorPrimitiveKind.hodge_project, hodge.slots[0].signature.kind);
    try testing.expectEqual(@as(u8, 3), hodge.slots[0].signature.action.input_rank);
    try testing.expectEqual(@as(u8, 2), hodge.slots[0].signature.action.gamma_rank);
    try testing.expectEqual(@as(u8, 5), hodge.slots[0].signature.action.output_rank);
    try testing.expectEqual(rendering.DualityTag.self_dual, hodge.slots[0].signature.action.duality);
}

test "projector constructor accepts odd-rank form-spinor chirality flip" {
    const testing = std.testing;

    const spec: TensorSpinorProjectionSpec = .{
        .operator_id = 46,
        .left = 10,
        .right = 11,
        .output = 12,
        .orthogonal_dimension = 10,
        .left_has_spinor = false,
        .right_chirality = 2,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_count = 1,
        .form_rank = 0,
        .form_count = 0,
        .form_mask = 0,
        .form_profile = 0,
        .tower_power = 1,
        .chirality = 1,
    };

    try testing.expectEqual(@as(u16, 1), tensorSpinorProjectionTermCount(spec));
    const program = try compileStructuralProjectorProgram(structuralProjectorSpecFromTensorSpinor(spec));
    try testing.expectEqual(ProjectorPrimitiveKind.spinor_tower_contract_adjoint, program.candidates[0].slots[0].kind);
    try testing.expectEqual(tensorFormRankBlock(10, 3), program.candidates[0].slots[0].auxiliary_block);
}

test "projector constructor keeps unsupported tensor-form projections compact outside expanded streaming" {
    const testing = std.testing;

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);

    const lowered = try appendTensorFormProjectionExpression(testing.allocator, &atoms, .{
        .operator_id = 17,
        .left = 1,
        .right = 2,
        .output = 3,
        .orthogonal_dimension = 10,
        .input_form_profile = @as(u128, 1) << 8,
        .input_form_mask = 0b100,
        .output_form_profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 8),
        .output_form_count = 2,
        .output_form_rank = 1,
        .output_duality = .anti_self_dual,
        .chirality = 1,
    });
    try testing.expect(!lowered);
    try testing.expectEqual(@as(usize, 1), atoms.items.len);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).tensor_form_projection, std.meta.activeTag(atoms.items[0]));
}

test "projector constructor emits vector-spinor trace subtraction terms" {
    const testing = std.testing;

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);

    const spec: VectorSpinorTracelessSpec = .{
        .operator_id = 11,
        .vector = 2,
        .spinor = 3,
        .orthogonal_dimension = 10,
        .chirality = 2,
    };
    try testing.expectEqual(@as(u16, 2), vectorSpinorTracelessTermCount(spec));

    const identity_coefficient = try appendVectorSpinorTracelessTerm(testing.allocator, &atoms, spec, 0);
    try testing.expectEqual(rendering.rationalOne(), identity_coefficient);
    try testing.expectEqual(@as(usize, 1), atoms.items.len);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).vector_spinor_identity, std.meta.activeTag(atoms.items[0]));

    atoms.clearRetainingCapacity();
    const trace_coefficient = try appendVectorSpinorTracelessTerm(testing.allocator, &atoms, spec, 1);
    try testing.expectEqual(@as(i32, -1), rendering.rationalValue(trace_coefficient).numerator);
    try testing.expectEqual(@as(u32, 10), rendering.rationalValue(trace_coefficient).denominator);
    try testing.expectEqual(@as(usize, 1), atoms.items.len);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).gamma_trace, std.meta.activeTag(atoms.items[0]));
}

const Rank2VectorOperator = struct {
    identity: Rational = .{ .numerator = 0, .denominator = 1 },
    swap: Rational = .{ .numerator = 0, .denominator = 1 },
    trace: Rational = .{ .numerator = 0, .denominator = 1 },
};

fn rank2VectorOperatorCompose(dimension: u16, left: Rank2VectorOperator, right: Rank2VectorOperator) !Rank2VectorOperator {
    var out: Rank2VectorOperator = .{};
    out.identity = try out.identity.add(try left.identity.mul(right.identity));
    out.identity = try out.identity.add(try left.swap.mul(right.swap));
    out.swap = try out.swap.add(try left.identity.mul(right.swap));
    out.swap = try out.swap.add(try left.swap.mul(right.identity));

    var trace_coefficient = try left.identity.mul(right.trace);
    trace_coefficient = try trace_coefficient.add(try left.swap.mul(right.trace));
    trace_coefficient = try trace_coefficient.add(try left.trace.mul(right.identity));
    trace_coefficient = try trace_coefficient.add(try left.trace.mul(right.swap));
    trace_coefficient = try trace_coefficient.add(try (try left.trace.mul(right.trace)).mul(try Rational.init(dimension, 1)));
    out.trace = trace_coefficient;
    return out;
}

fn expectRank2VectorOperatorEqual(expected: Rank2VectorOperator, actual: Rank2VectorOperator) !void {
    const testing = std.testing;
    try testing.expect(rationalValueEql(expected.identity, actual.identity));
    try testing.expect(rationalValueEql(expected.swap, actual.swap));
    try testing.expect(rationalValueEql(expected.trace, actual.trace));
}

fn rank2GramDerivedOperator(spec: VectorSlotProjectorSpec, program: VectorBrauerProgram) !Rank2VectorOperator {
    var gram_program = program;
    gram_program.term_count = 0;
    gram_program.terms = [_]VectorBrauerTerm{.{}} ** max_vector_brauer_terms;
    try appendGramDerivedVectorBrauerTerms(&gram_program, spec);
    return .{
        .identity = try rank2TermKernelValue(spec, gram_program, .{ 0, 1, 0, 0 }, .{ 0, 1, 0, 0 }),
        .swap = try rank2TermKernelValue(spec, gram_program, .{ 1, 0, 0, 0 }, .{ 0, 1, 0, 0 }),
        .trace = try rank2TermKernelValue(spec, gram_program, .{ 1, 1, 0, 0 }, .{ 0, 0, 0, 0 }),
    };
}

fn rank2GramComposedOperator(spec: VectorSlotProjectorSpec, program: VectorBrauerProgram) !Rank2VectorOperator {
    var composed_program = program;
    composed_program.term_count = 0;
    composed_program.terms = [_]VectorBrauerTerm{.{}} ** max_vector_brauer_terms;
    var row: u8 = 0;
    while (row < program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.pivot_count) : (column += 1) {
            const coefficient = program.inverse_gram[@as(usize, row) * program.pivot_count + column];
            if (coefficient.numerator == 0) continue;
            const left = program.candidates[program.pivots[row]];
            const right = program.candidates[program.pivots[column]];
            var left_word_index: u8 = 0;
            while (left_word_index < left.word_count) : (left_word_index += 1) {
                var right_word_index: u8 = 0;
                while (right_word_index < right.word_count) : (right_word_index += 1) {
                    var word_coefficient = try coefficient.mul(left.words[left_word_index].coefficient);
                    word_coefficient = try word_coefficient.mul(right.words[right_word_index].coefficient);
                    const term = try materializeVectorBrauerComposedWordPairTerm(spec, left.words[left_word_index], right.words[right_word_index], word_coefficient);
                    try appendMergedVectorBrauerTerm(&composed_program, term);
                }
            }
        }
    }
    return .{
        .identity = try rank2TermKernelValue(spec, composed_program, .{ 0, 1, 0, 0 }, .{ 0, 1, 0, 0 }),
        .swap = try rank2TermKernelValue(spec, composed_program, .{ 1, 0, 0, 0 }, .{ 0, 1, 0, 0 }),
        .trace = try rank2TermKernelValue(spec, composed_program, .{ 1, 1, 0, 0 }, .{ 0, 0, 0, 0 }),
    };
}

fn materializeVectorBrauerComposedWordPairTerm(spec: VectorSlotProjectorSpec, left_word: BrauerWord, right_word: BrauerWord, coefficient: Rational) !VectorBrauerTerm {
    const rank = vectorYoungRank(spec) orelse return error.UnsupportedStructuralProjectorTerm;
    var graph: BrauerContraction = .{};
    graph.init(rank);
    try graph.addCompositionLeftWord(rank, left_word);
    try graph.addCompositionRightAdjointWord(rank, right_word);
    var term = try vectorBrauerTerm(coefficient);
    const loops = try appendComposedVectorBrauerTermAtoms(&term, spec, &graph, rank);
    term.coefficient = try term.coefficient.mul(try powRational(spec.dimension, loops));
    canonicalizeVectorBrauerTerm(&term);
    return term;
}

fn rank2TermKernelValue(spec: VectorSlotProjectorSpec, program: VectorBrauerProgram, source_values: [max_vector_young_boxes]usize, output_values: [max_vector_young_boxes]usize) !Rational {
    var acc = Rational.zero();
    var term_index: u8 = 0;
    while (term_index < program.term_count) : (term_index += 1) {
        const term = program.terms[term_index];
        if (!try vectorTermMatches(spec, term, source_values, output_values)) continue;
        acc = try acc.add(term.coefficient);
    }
    return acc;
}

fn rationalValueEql(left: Rational, right: Rational) bool {
    return left.numerator == right.numerator and left.denominator == right.denominator;
}

fn expectTensorWordGramMatchesVectorGram(program: TensorChannelProgram) !void {
    const testing = std.testing;
    var tensor_program = program;
    tensor_program.pivot_count = 0;
    tensor_program.pivots = [_]u8{0} ** max_program_pivots;
    tensor_program.inverse_gram = [_]Rational{Rational.zero()} ** max_program_gram_entries;
    try compileTensorWordGram(&tensor_program);

    try testing.expectEqual(program.vector_program.pivot_count, tensor_program.pivot_count);
    var pivot_index: u8 = 0;
    while (pivot_index < program.vector_program.pivot_count) : (pivot_index += 1) {
        try testing.expectEqual(program.vector_program.pivots[pivot_index], tensor_program.pivots[pivot_index]);
    }

    var row: u8 = 0;
    while (row < program.candidate_count) : (row += 1) {
        var column: u8 = 0;
        while (column < program.candidate_count) : (column += 1) {
            const tensor_value = try tensorCandidateInnerProduct(program, program.words[row], program.words[column]);
            const vector_value = try brauerCandidateInnerProduct(
                program.dimension,
                program.rank,
                program.vector_program.candidates[row],
                program.vector_program.candidates[column],
            );
            try testing.expect(rationalValueEql(vector_value, tensor_value));
        }
    }

    row = 0;
    while (row < tensor_program.pivot_count) : (row += 1) {
        var column: u8 = 0;
        while (column < tensor_program.pivot_count) : (column += 1) {
            const index = @as(usize, row) * tensor_program.pivot_count + column;
            try testing.expect(rationalValueEql(program.vector_program.inverse_gram[index], tensor_program.inverse_gram[index]));
        }
    }

    try expectTensorWordTermsMatchGramProgram(program);
}

fn expectTensorWordTermsMatchGramProgram(program: TensorChannelProgram) !void {
    const testing = std.testing;
    var gram_program = program.vector_program;
    gram_program.pivot_count = program.pivot_count;
    gram_program.pivots = program.pivots;
    gram_program.inverse_gram = program.inverse_gram;
    try appendGramDerivedVectorBrauerTerms(&gram_program, program.vector_spec);
    const merged_program = try materializeTensorChannelProgramTerms(&program);
    try testing.expectEqual(gram_program.term_count, merged_program.term_count);
    try testing.expect(program.term_count >= merged_program.term_count);

    var seen = [_]bool{false} ** max_vector_brauer_terms;
    var term_index: u8 = 0;
    while (term_index < merged_program.term_count) : (term_index += 1) {
        const tensor_term = merged_program.terms[term_index];
        var matched = false;
        var vector_index: u8 = 0;
        while (vector_index < gram_program.term_count) : (vector_index += 1) {
            if (seen[vector_index]) continue;
            const vector_term = gram_program.terms[vector_index];
            if (!rationalValueEql(vector_term.coefficient, tensor_term.coefficient)) continue;
            if (!vectorBrauerTermAtomsEql(vector_term, tensor_term)) continue;
            seen[vector_index] = true;
            matched = true;
            break;
        }
        try testing.expect(matched);
    }
}

const hook_test_dimension = 5;
const HookTestTensor = [hook_test_dimension][hook_test_dimension][hook_test_dimension]Rational;
const WeylTestTensor = [hook_test_dimension][hook_test_dimension][hook_test_dimension][hook_test_dimension]Rational;

const VectorBrauerTermBuffer = struct {
    count: u8 = 0,
    terms: [max_vector_brauer_terms]VectorBrauerTerm = [_]VectorBrauerTerm{.{}} ** max_vector_brauer_terms,
};

fn materializeVectorBrauerProgramTerms(spec: VectorSlotProjectorSpec, program: VectorBrauerProgram) !VectorBrauerTermBuffer {
    if (program.term_count > max_vector_brauer_terms) return error.ProjectorProgramTooLarge;
    var buffer: VectorBrauerTermBuffer = .{};
    while (buffer.count < program.term_count) : (buffer.count += 1) {
        buffer.terms[buffer.count] = try materializeVectorBrauerProgramTerm(spec, program, buffer.count);
    }
    return buffer;
}

fn hookTestZeroTensor() HookTestTensor {
    return [_][hook_test_dimension][hook_test_dimension]Rational{[_][hook_test_dimension]Rational{[_]Rational{Rational.zero()} ** hook_test_dimension} ** hook_test_dimension} ** hook_test_dimension;
}

fn hookTestSource(values: *const HookTestTensor, a: usize, b: usize, c: usize) Rational {
    return values[a][b][c];
}

fn hookTestTrace(values: *const HookTestTensor, c: usize) !Rational {
    var acc = Rational.zero();
    var d: usize = 0;
    while (d < hook_test_dimension) : (d += 1) {
        acc = try acc.add(hookTestSource(values, d, d, c));
    }
    return acc;
}

fn hookTestApplyAt(values: *const HookTestTensor, a: usize, b: usize, c: usize) !Rational {
    const two_thirds = try Rational.init(2, 3);
    const minus_one_third = try Rational.init(-1, 3);
    const trace_scale = try Rational.init(1, hook_test_dimension - 1);

    var acc = try two_thirds.mul(hookTestSource(values, a, b, c));
    acc = try acc.add(try minus_one_third.mul(hookTestSource(values, b, c, a)));
    acc = try acc.add(try minus_one_third.mul(hookTestSource(values, c, a, b)));
    if (a == b) acc = try acc.sub(try trace_scale.mul(try hookTestTrace(values, c)));
    if (a == c) acc = try acc.add(try trace_scale.mul(try hookTestTrace(values, b)));
    return acc;
}

fn hookTestApply(values: *const HookTestTensor) !HookTestTensor {
    var out = hookTestZeroTensor();
    var a: usize = 0;
    while (a < hook_test_dimension) : (a += 1) {
        var b: usize = 0;
        while (b < hook_test_dimension) : (b += 1) {
            var c: usize = 0;
            while (c < hook_test_dimension) : (c += 1) {
                out[a][b][c] = try hookTestApplyAt(values, a, b, c);
            }
        }
    }
    return out;
}

fn expectHookTestZero(value: Rational) !void {
    try std.testing.expectEqual(@as(i64, 0), value.numerator);
    try std.testing.expectEqual(@as(i64, 1), value.denominator);
}

fn weylTestZeroTensor() WeylTestTensor {
    return [_][hook_test_dimension][hook_test_dimension][hook_test_dimension]Rational{[_][hook_test_dimension][hook_test_dimension]Rational{[_][hook_test_dimension]Rational{[_]Rational{Rational.zero()} ** hook_test_dimension} ** hook_test_dimension} ** hook_test_dimension} ** hook_test_dimension;
}

fn weylTestSourceValue(values: *const WeylTestTensor, source_values: [4]usize) Rational {
    return values[source_values[0]][source_values[1]][source_values[2]][source_values[3]];
}

fn vectorTermSourceValue(spec: VectorSlotProjectorSpec, block: rendering.IndexBlockId, slot: u8, source_values: [max_vector_young_boxes]usize) !usize {
    if (block == spec.left and slot < spec.left_slot_count) return source_values[slot];
    if (block == spec.right and slot < spec.right_slot_count) return source_values[spec.left_slot_count + slot];
    return error.InvalidVectorBrauerTestSource;
}

fn vectorTermOutputValue(spec: VectorSlotProjectorSpec, block: rendering.IndexBlockId, slot: u8, output_values: [max_vector_young_boxes]usize) !usize {
    if (block == spec.output and slot < spec.shape.box_count) return output_values[slot];
    return error.InvalidVectorBrauerTestOutput;
}

fn vectorTermBlockValue(spec: VectorSlotProjectorSpec, block: rendering.IndexBlockId, slot: u8, source_values: [max_vector_young_boxes]usize, output_values: [max_vector_young_boxes]usize) !usize {
    if (block == spec.output) return vectorTermOutputValue(spec, block, slot, output_values);
    return vectorTermSourceValue(spec, block, slot, source_values);
}

fn vectorTermMatches(spec: VectorSlotProjectorSpec, term: VectorBrauerTerm, source_values: [max_vector_young_boxes]usize, output_values: [max_vector_young_boxes]usize) !bool {
    var atom_index: u8 = 0;
    while (atom_index < term.atom_count) : (atom_index += 1) {
        const atom = term.atoms[atom_index];
        switch (atom.kind) {
            .delta => if (try vectorTermSourceValue(spec, atom.upper, atom.upper_slot, source_values) != try vectorTermOutputValue(spec, atom.lower, atom.lower_slot, output_values)) return false,
            .metric => {
                const left_value = try vectorTermBlockValue(spec, atom.left, atom.left_slot, source_values, output_values);
                const right_value = try vectorTermBlockValue(spec, atom.right, atom.right_slot, source_values, output_values);
                if (left_value != right_value) return false;
            },
            .hodge_star => return error.UnsupportedTensorBridge,
        }
    }
    return true;
}

fn weylProgramApplyAt(spec: VectorSlotProjectorSpec, program: VectorBrauerProgram, values: *const WeylTestTensor, output_values: [max_vector_young_boxes]usize) !Rational {
    var acc = Rational.zero();
    var a: usize = 0;
    while (a < hook_test_dimension) : (a += 1) {
        var b: usize = 0;
        while (b < hook_test_dimension) : (b += 1) {
            var c: usize = 0;
            while (c < hook_test_dimension) : (c += 1) {
                var d: usize = 0;
                while (d < hook_test_dimension) : (d += 1) {
                    var source_values = [_]usize{0} ** max_vector_young_boxes;
                    source_values[0] = a;
                    source_values[1] = b;
                    source_values[2] = c;
                    source_values[3] = d;
                    const source = weylTestSourceValue(values, .{ a, b, c, d });
                    if (source.numerator == 0) continue;
                    var term_index: u8 = 0;
                    while (term_index < program.term_count) : (term_index += 1) {
                        const term = program.terms[term_index];
                        if (!try vectorTermMatches(spec, term, source_values, output_values)) continue;
                        acc = try acc.add(try term.coefficient.mul(source));
                    }
                }
            }
        }
    }
    return acc;
}

fn weylProgramApply(spec: VectorSlotProjectorSpec, program: VectorBrauerProgram, values: *const WeylTestTensor) !WeylTestTensor {
    var out = weylTestZeroTensor();
    var a: usize = 0;
    while (a < hook_test_dimension) : (a += 1) {
        var b: usize = 0;
        while (b < hook_test_dimension) : (b += 1) {
            var c: usize = 0;
            while (c < hook_test_dimension) : (c += 1) {
                var d: usize = 0;
                while (d < hook_test_dimension) : (d += 1) {
                    var output_values = [_]usize{0} ** max_vector_young_boxes;
                    output_values[0] = a;
                    output_values[1] = b;
                    output_values[2] = c;
                    output_values[3] = d;
                    out[a][b][c][d] = try weylProgramApplyAt(spec, program, values, output_values);
                }
            }
        }
    }
    return out;
}

fn weylTestTrace(values: *const WeylTestTensor, b: usize, d: usize) !Rational {
    var acc = Rational.zero();
    var a: usize = 0;
    while (a < hook_test_dimension) : (a += 1) {
        acc = try acc.add(values[a][b][a][d]);
    }
    return acc;
}

fn expectDescriptorRows(descriptor: OrthogonalTensorDescriptor, expected: []const u8) !void {
    try std.testing.expectEqual(@as(u8, @intCast(expected.len)), descriptor.young_row_count);
    var index: usize = 0;
    while (index < expected.len) : (index += 1) {
        try std.testing.expectEqual(expected[index], descriptor.young_rows[index]);
    }
}

fn expectYoungCandidateQuasiIdempotent(shape: YoungShape, expected_scale: i64) !void {
    const testing = std.testing;
    var candidates: BrauerCandidateBuffer = .{};
    try appendVectorYoungPermutationCandidates(shape, shape.box_count, &candidates);
    try testing.expectEqual(@as(u8, 1), candidates.count);

    const young = candidates.candidates[0];
    const square = try composeBrauerCandidates(shape.box_count, 10, young, young);
    const scale = try brauerCandidateProportionalScale(young, square);
    try testing.expectEqual(expected_scale, scale.numerator);
    try testing.expectEqual(@as(i64, 1), scale.denominator);

    const normalized = try normalizedBrauerIdempotentCandidate(shape.box_count, 10, young);
    const normalized_square = try composeBrauerCandidates(shape.box_count, 10, normalized, normalized);
    try testing.expect(brauerCandidateEql(normalized, normalized_square));
}

fn expectTraceFreeYoungProjector(shape: YoungShape, dimension: u16) !void {
    const testing = std.testing;
    var candidates: BrauerCandidateBuffer = .{};
    try appendVectorYoungPermutationCandidates(shape, shape.box_count, &candidates);
    try testing.expectEqual(@as(u8, 1), candidates.count);

    const projector = try traceFreeBrauerProjectorCandidateForShape(shape, dimension, candidates.candidates[0]);
    const square = try composeBrauerCandidates(shape.box_count, dimension, projector, projector);
    try testing.expect(brauerCandidateEql(projector, square));

    var trace_generators: BrauerCandidateBuffer = .{};
    try appendVectorYoungTraceCandidatesForShape(shape, &trace_generators);
    try assertTraceFreeBrauerCandidate(shape.box_count, dimension, projector, trace_generators);
}

test "projector constructor composes Young candidates by generic Brauer algebra" {
    try expectYoungCandidateQuasiIdempotent(.{ .row_count = 1, .rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 }, .box_count = 2 }, 2);
    try expectYoungCandidateQuasiIdempotent(.{ .row_count = 2, .rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 }, .box_count = 2 }, 2);
    try expectYoungCandidateQuasiIdempotent(.{ .row_count = 2, .rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 }, .box_count = 3 }, 3);
    try expectYoungCandidateQuasiIdempotent(.{ .row_count = 2, .rows = .{ 3, 1, 0, 0, 0, 0, 0, 0 }, .box_count = 4 }, 8);
    try expectYoungCandidateQuasiIdempotent(.{ .row_count = 2, .rows = .{ 2, 2, 0, 0, 0, 0, 0, 0 }, .box_count = 4 }, 12);
}

test "projector constructor solves trace-free Young projectors by generic Brauer constraints" {
    try expectTraceFreeYoungProjector(.{ .row_count = 1, .rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 }, .box_count = 2 }, 10);
    try expectTraceFreeYoungProjector(.{ .row_count = 2, .rows = .{ 1, 1, 0, 0, 0, 0, 0, 0 }, .box_count = 2 }, 10);
    try expectTraceFreeYoungProjector(.{ .row_count = 2, .rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 }, .box_count = 3 }, 10);
    try expectTraceFreeYoungProjector(.{ .row_count = 2, .rows = .{ 3, 1, 0, 0, 0, 0, 0, 0 }, .box_count = 4 }, 10);
    try expectTraceFreeYoungProjector(.{ .row_count = 2, .rows = .{ 2, 2, 0, 0, 0, 0, 0, 0 }, .box_count = 4 }, 10);
    try expectTraceFreeYoungProjector(.{ .row_count = 5, .rows = .{ 1, 1, 1, 1, 1, 0, 0, 0 }, .box_count = 5 }, 9);
}

test "projector constructor streams a beyond-four-box exterior vector projector" {
    const testing = std.testing;
    const spec: VectorSlotProjectorSpec = .{
        .operator_id = 98,
        .dimension = 9,
        .left = 1,
        .left_slot_count = 2,
        .right = 2,
        .right_slot_count = 3,
        .output = 3,
        .shape = .{ .row_count = 5, .rows = .{ 1, 1, 1, 1, 1, 0, 0, 0 }, .box_count = 5 },
    };
    const program = try compileVectorYoungBrauerProgram(spec);
    try testing.expect(program.term_count != 0);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    _ = try appendVectorSlotProjectorTerm(testing.allocator, &atoms, spec, 0);
    try testing.expectEqual(@as(usize, 5), atoms.items.len);
    for (atoms.items) |atom| {
        switch (atom) {
            .vector_slot_delta => {},
            else => return error.ExpectedVectorSlotPrimitive,
        }
    }
}

test "projector constructor reports typed Brauer cap for five-box trace closure beyond word cap" {
    const testing = std.testing;
    var candidates: BrauerCandidateBuffer = .{};
    const shape: YoungShape = .{ .row_count = 3, .rows = .{ 3, 1, 1, 0, 0, 0, 0, 0 }, .box_count = 5 };
    try appendVectorYoungPermutationCandidates(shape, shape.box_count, &candidates);
    try testing.expectEqual(@as(u8, 1), candidates.count);

    var trace_generators: BrauerCandidateBuffer = .{};
    try appendVectorYoungTraceCandidatesForShape(shape, &trace_generators);
    try testing.expect(trace_generators.count < 10);

    try testing.expectError(error.UnsupportedTensorBrauerCandidateCap, traceFreeBrauerProjectorCandidateForShape(shape, 9, candidates.candidates[0]));
    try testing.expectError(error.UnsupportedTensorBrauerCandidateCap, traceFreeBrauerProjectorCandidate(shape.box_count, 9, candidates.candidates[0]));
}

test "projector constructor streams five-box Young terms past stored-program cap" {
    const testing = std.testing;
    const spec: VectorSlotProjectorSpec = .{
        .operator_id = 99,
        .dimension = 9,
        .left = 1,
        .left_slot_count = 2,
        .right = 2,
        .right_slot_count = 3,
        .output = 3,
        .shape = .{ .row_count = 3, .rows = .{ 3, 1, 1, 0, 0, 0, 0, 0 }, .box_count = 5 },
    };
    const term_count = try countVectorYoungProjectionTerms(spec);
    try testing.expect(term_count > max_vector_brauer_terms);
    try testing.expectError(error.UnsupportedTensorPrimitiveTermCap, compileVectorYoungBrauerProgram(spec));

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    _ = try appendVectorSlotProjectorTerm(testing.allocator, &atoms, spec, max_vector_brauer_terms);
    try testing.expect(atoms.items.len != 0);
    for (atoms.items) |atom| {
        switch (atom) {
            .vector_slot_delta, .vector_slot_metric => {},
            else => return error.ExpectedVectorSlotPrimitive,
        }
    }
}

test "projector constructor parses B/D tensor Dynkin labels into Young descriptors" {
    const testing = std.testing;
    const d5: symmetry.SimpleLieAlgebra = .{ .family = .d, .rank = 5 };
    const b4: symmetry.SimpleLieAlgebra = .{ .family = .b, .rank = 4 };

    const symmetric = try orthogonalTensorDescriptorFromDynkin(d5, &.{ 2, 0, 0, 0, 0 });
    try testing.expectEqual(OrthogonalTensorKind.vector_young, symmetric.kind);
    try testing.expectEqual(@as(u16, 10), symmetric.dimension);
    try testing.expectEqual(@as(u8, 2), symmetric.young_box_count);
    try expectDescriptorRows(symmetric, &.{2});
    try testing.expectEqual(@as(u8, 2), symmetric.column_count);
    try testing.expectEqual(@as(u8, 1), symmetric.column_heights[0]);
    try testing.expectEqual(@as(u8, 1), symmetric.column_heights[1]);

    const hook = try orthogonalTensorDescriptorFromDynkin(d5, &.{ 1, 1, 0, 0, 0 });
    try testing.expectEqual(OrthogonalTensorKind.vector_young, hook.kind);
    try testing.expectEqual(@as(u8, 3), hook.young_box_count);
    try expectDescriptorRows(hook, &.{ 2, 1 });
    try testing.expectEqual(@as(u8, 2), hook.column_count);
    try testing.expectEqual(@as(u8, 2), hook.column_heights[0]);
    try testing.expectEqual(@as(u8, 1), hook.column_heights[1]);

    const weyl = try orthogonalTensorDescriptorFromDynkin(d5, &.{ 0, 2, 0, 0, 0 });
    try testing.expectEqual(OrthogonalTensorKind.vector_young, weyl.kind);
    try testing.expectEqual(@as(u8, 4), weyl.young_box_count);
    try expectDescriptorRows(weyl, &.{ 2, 2 });

    const b4_weyl = try orthogonalTensorDescriptorFromDynkin(b4, &.{ 0, 2, 0, 0 });
    try testing.expectEqual(@as(u16, 9), b4_weyl.dimension);
    try expectDescriptorRows(b4_weyl, &.{ 2, 2 });
}

test "projector constructor tensor descriptor covers beyond four boxes and rejects spinor or over-cap labels" {
    const testing = std.testing;
    const d6: symmetry.SimpleLieAlgebra = .{ .family = .d, .rank = 6 };
    const b4: symmetry.SimpleLieAlgebra = .{ .family = .b, .rank = 4 };

    const six_box = try orthogonalTensorDescriptorFromDynkin(d6, &.{ 0, 0, 0, 0, 1, 1 });
    try testing.expectEqual(OrthogonalTensorKind.exterior_form, six_box.kind);
    try testing.expectEqual(@as(u8, 5), six_box.young_box_count);
    try testing.expectEqual(@as(u8, 5), six_box.form_rank);
    try expectDescriptorRows(six_box, &.{ 1, 1, 1, 1, 1 });

    try testing.expectError(error.UnsupportedTensorSpinorLabel, orthogonalTensorDescriptorFromDynkin(b4, &.{ 0, 0, 0, 1 }));
    try testing.expectError(error.UnsupportedTensorShapeOverCap, orthogonalTensorDescriptorFromDynkin(d6, &.{ 9, 0, 0, 0, 0, 0 }));
}

test "projector constructor composes rank-2 vector Young projectors exactly" {
    const testing = std.testing;
    const dimension: u16 = 10;
    const half = try Rational.init(1, 2);
    const minus_half = try Rational.init(-1, 2);
    const inv_dimension = try Rational.init(1, dimension);
    const minus_inv_dimension = try Rational.init(-1, dimension);

    const trace: Rank2VectorOperator = .{ .trace = inv_dimension };
    const antisymmetric: Rank2VectorOperator = .{ .identity = half, .swap = minus_half };
    const symmetric_traceless: Rank2VectorOperator = .{ .identity = half, .swap = half, .trace = minus_inv_dimension };

    try expectRank2VectorOperatorEqual(trace, try rank2VectorOperatorCompose(dimension, trace, trace));
    try expectRank2VectorOperatorEqual(antisymmetric, try rank2VectorOperatorCompose(dimension, antisymmetric, antisymmetric));
    try expectRank2VectorOperatorEqual(symmetric_traceless, try rank2VectorOperatorCompose(dimension, symmetric_traceless, symmetric_traceless));
    try expectRank2VectorOperatorEqual(.{}, try rank2VectorOperatorCompose(dimension, trace, antisymmetric));
    try expectRank2VectorOperatorEqual(.{}, try rank2VectorOperatorCompose(dimension, trace, symmetric_traceless));
    try expectRank2VectorOperatorEqual(.{}, try rank2VectorOperatorCompose(dimension, antisymmetric, symmetric_traceless));

    const symmetric_spec: VectorSlotProjectorSpec = .{
        .operator_id = 91,
        .dimension = dimension,
        .left = 1,
        .right = 2,
        .output = 3,
        .shape = .{ .row_count = 1, .rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 }, .box_count = 2 },
    };
    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    const coefficient = try appendVectorSlotProjectorTerm(testing.allocator, &atoms, symmetric_spec, 2);
    try testing.expectEqual(@as(i128, -1), coefficient.numerator);
    try testing.expectEqual(@as(u128, dimension), coefficient.denominator);
    try testing.expectEqual(@as(usize, 2), atoms.items.len);
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).vector_slot_metric, std.meta.activeTag(atoms.items[0]));
    try testing.expectEqual(std.meta.Tag(rendering.SymbolicAtom).vector_slot_metric, std.meta.activeTag(atoms.items[1]));
}

test "projector constructor reports unsupported over-limit vector Young shapes" {
    const testing = std.testing;

    const spec: VectorSlotProjectorSpec = .{
        .operator_id = 92,
        .dimension = 10,
        .left = 1,
        .left_slot_count = 4,
        .right = 2,
        .right_slot_count = 5,
        .output = 3,
        .shape = .{ .row_count = 1, .rows = .{ 9, 0, 0, 0, 0, 0, 0, 0 }, .box_count = 9 },
    };

    try testing.expectEqual(@as(u8, 0), vectorSlotProjectorTermCount(spec));
    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    try testing.expectError(error.UnsupportedTensorShapeOverCap, appendVectorSlotProjectorTerm(testing.allocator, &atoms, spec, 0));
}

test "projector constructor preserves structural tensor shape cap errors through cache" {
    const testing = std.testing;

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();

    const spec: StructuralProjectorSpec = .{
        .operator_id = 921,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = @as(u128, 1) << 12,
            .form_mask = @as(u64, 1) << 3,
            .form_count = 1,
            .form_rank = 4,
        },
        .right = .{
            .index = 2,
            .form_profile = @as(u128, 1) << 16,
            .form_mask = @as(u64, 1) << 4,
            .form_count = 1,
            .form_rank = 5,
        },
        .output = .{
            .index = 3,
            .young_row_count = 1,
            .young_rows = .{ 9, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 9,
        },
    };

    try testing.expectError(error.UnsupportedTensorShapeOverCap, cache.termCount(spec));
    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    try testing.expectError(error.UnsupportedTensorShapeOverCap, cache.appendTerm(&atoms, spec, 0));
}

test "projector constructor rejects odd mixed tensor-only Brauer boundaries" {
    const testing = std.testing;

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();

    const spec: StructuralProjectorSpec = .{
        .operator_id = 922,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4),
            .form_mask = 0b11,
            .form_count = 2,
        },
        .right = .{ .index = 2 },
        .output = .{ .index = 3 },
    };

    const channel = try tensorCompilerChannelFromStructural(spec);
    const tensor_channel = try liveTensorOnlyChannelFromCompilerChannel(channel);
    try testing.expectEqual(@as(u8, 3), tensor_channel.input_slot_count);
    try testing.expectEqual(@as(u8, 0), tensor_channel.output_slot_count);
    try testing.expectError(error.UnsupportedStructuralProjectorTerm, compileGeneralTensorOnlyBrauerProgram(tensor_channel));

    try testing.expectEqual(@as(u16, 0), structuralProjectorTermCount(spec));
    try testing.expectError(error.UnsupportedStructuralProjectorTerm, cache.termCount(spec));
    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    try testing.expectError(error.UnsupportedStructuralProjectorTerm, cache.appendTerm(&atoms, spec, 0));
    try testing.expectError(error.UnsupportedStructuralProjectorTerm, appendStructuralProjectorTerm(testing.allocator, &atoms, spec, 0));
}

test "projector constructor exposes compressed form source slots to Young channel" {
    const testing = std.testing;

    const spec: StructuralProjectorSpec = .{
        .operator_id = 923,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4),
            .form_mask = 0b11,
            .form_count = 2,
        },
        .right = .{ .index = 2 },
        .output = .{
            .index = 3,
            .young_row_count = 2,
            .young_rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
    };

    const term_count = structuralProjectorTermCount(spec);
    try testing.expect(term_count != 0);
    const channel = try tensorCompilerChannelFromStructural(spec);
    const tensor_channel = try liveTensorOnlyChannelFromCompilerChannel(channel);
    var general_program = try compileGeneralTensorOnlyBrauerProgram(tensor_channel);
    defer general_program.deinit();
    try testing.expectEqual(general_program.term_count, term_count);

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    try testing.expectEqual(term_count, try cache.termCount(spec));
    try testing.expectEqual(@as(usize, 1), cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), cache.vector_entries.items.len);

    const vector_spec = vectorSlotProjectorSpecFromChannel(channel).?;
    try testing.expectEqual(@as(u8, 3), vector_spec.left_slot_count);
    try testing.expectEqual((@as(u128, 1) << 0) | (@as(u128, 1) << 4), vector_spec.left_form_profile);
    const tensor_program = try compileDiagnosticFallbackTensorChannelProgram(channel);
    try testing.expectEqual(CachedVectorProgramKind.projector, tensor_program.kind);
    try testing.expectEqual(@as(u8, 2), tensor_program.words[0].primitive_count);
    try testing.expectEqual(TensorPrimitiveKind.form_bridge, tensor_program.words[0].primitives[0].kind);
    try testing.expectEqual(@as(u8, 0), tensor_program.words[0].primitives[0].candidate_index);
    try testing.expectEqual(TensorPrimitiveKind.vector_young_output, tensor_program.words[0].primitives[1].kind);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var saw_rank_one_block = false;
    var saw_rank_two_block = false;
    var term_index: u16 = 0;
    while (term_index < term_count) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try appendStructuralProjectorTerm(testing.allocator, &atoms, spec, term_index);
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_delta => |delta| {
                    if (delta.upper == tensorFormRankBlock(spec.left.index, 1)) saw_rank_one_block = true;
                    if (delta.upper == tensorFormRankBlock(spec.left.index, 2)) saw_rank_two_block = true;
                },
                .vector_slot_metric => {},
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
    try testing.expect(saw_rank_one_block);
    try testing.expect(saw_rank_two_block);
}

test "projector constructor routes mixed form scalar pairing through tensor-only cache" {
    const testing = std.testing;

    const profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4);
    const spec: StructuralProjectorSpec = .{
        .operator_id = 9231,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = profile,
            .form_mask = 0b11,
            .form_count = 2,
        },
        .right = .{
            .index = 2,
            .form_profile = profile,
            .form_mask = 0b11,
            .form_count = 2,
        },
        .output = .{ .index = 3 },
    };

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();

    const term_count = try cache.termCount(spec);
    try testing.expect(term_count != 0);
    try testing.expectEqual(@as(usize, 1), cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), cache.vector_entries.items.len);
    try testing.expect(cache.tensor_only_entries.items[0].program.endpoint_action_count != 0);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    _ = try cache.appendTerm(&atoms, spec, 0);
    try testing.expect(atoms.items.len != 0);
    try testing.expectEqual(@as(usize, 1), cache.tensor_only_entries.items.len);
}

test "projector constructor routes repeated-rank mixed form multiplicities through tensor-only cache" {
    const testing = std.testing;

    const profile = @as(u128, 2) << 0;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 9232,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = profile,
            .form_mask = 0b1,
            .form_count = 2,
        },
        .right = .{
            .index = 2,
            .form_profile = profile,
            .form_mask = 0b1,
            .form_count = 2,
        },
        .output = .{ .index = 3 },
    };

    const channel = try tensorCompilerChannelFromStructural(spec);
    const tensor_channel = try liveTensorOnlyChannelFromCompilerChannel(channel);
    try testing.expectEqual(@as(u8, 2), tensor_channel.left.slot_count);
    try testing.expectEqual(tensorFormRankBlock(spec.left.index, 1), tensor_channel.left.layout.slots[0].block);
    try testing.expectEqual(tensorFormRankBlock(spec.left.index, 1), tensor_channel.left.layout.slots[1].block);
    try testing.expectEqual(@as(u8, 0), tensor_channel.left.layout.slots[0].slot);
    try testing.expectEqual(@as(u8, 1), tensor_channel.left.layout.slots[1].slot);
    try testing.expectEqual(@as(u8, 1), tensor_channel.left.row_count);
    try testing.expectEqual(@as(u8, 2), tensor_channel.left.rows[0]);

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    const term_count = try cache.termCount(spec);
    try testing.expect(term_count != 0);
    try testing.expectEqual(@as(usize, 1), cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), cache.vector_entries.items.len);
}

test "projector constructor returns mixed tensor-only size errors before fallback" {
    const testing = std.testing;

    const profile = @as(u128, 5) << 0;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 9233,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = profile,
            .form_mask = 0b1,
            .form_count = 5,
        },
        .right = .{
            .index = 2,
            .form_profile = profile,
            .form_mask = 0b1,
            .form_count = 5,
        },
        .output = .{ .index = 3 },
    };

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    try testing.expectError(error.ProjectorProgramTooLarge, cache.termCount(spec));
    try testing.expectEqual(@as(usize, 0), cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), cache.vector_entries.items.len);
}

test "projector constructor exposes compressed form target slots to Young channel" {
    const testing = std.testing;

    const output_profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4);
    const spec: StructuralProjectorSpec = .{
        .operator_id = 924,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 2,
            .young_rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
        .right = .{ .index = 2 },
        .output = .{
            .index = 3,
            .form_profile = output_profile,
            .form_mask = 0b11,
            .form_count = 2,
        },
    };

    const term_count = structuralProjectorTermCount(spec);
    try testing.expect(term_count != 0);
    const channel = try tensorCompilerChannelFromStructural(spec);
    const tensor_channel = try liveTensorOnlyChannelFromCompilerChannel(channel);
    var general_program = try compileGeneralTensorOnlyBrauerProgram(tensor_channel);
    defer general_program.deinit();
    try testing.expectEqual(general_program.term_count, term_count);

    var cache = StructuralProjectorProgramCache.init(testing.allocator);
    defer cache.deinit();
    try testing.expectEqual(term_count, try cache.termCount(spec));
    try testing.expectEqual(@as(usize, 1), cache.tensor_only_entries.items.len);
    try testing.expectEqual(@as(usize, 0), cache.vector_entries.items.len);

    const vector_spec = vectorSlotProjectorSpecFromChannel(channel).?;
    try testing.expectEqual(@as(u8, 3), vector_spec.shape.box_count);
    try testing.expectEqual(output_profile, vector_spec.output_form_profile);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var saw_rank_one_block = false;
    var saw_rank_two_block = false;
    var term_index: u16 = 0;
    while (term_index < term_count) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try appendStructuralProjectorTerm(testing.allocator, &atoms, spec, term_index);
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_delta => |delta| {
                    if (delta.lower == tensorFormRankBlock(spec.output.index, 1)) saw_rank_one_block = true;
                    if (delta.lower == tensorFormRankBlock(spec.output.index, 2)) saw_rank_two_block = true;
                },
                .vector_slot_metric => |metric| {
                    if (metric.left == tensorFormRankBlock(spec.output.index, 1) or metric.right == tensorFormRankBlock(spec.output.index, 1)) saw_rank_one_block = true;
                    if (metric.left == tensorFormRankBlock(spec.output.index, 2) or metric.right == tensorFormRankBlock(spec.output.index, 2)) saw_rank_two_block = true;
                },
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
    try testing.expect(saw_rank_one_block);
    try testing.expect(saw_rank_two_block);
}

test "projector constructor exposes two-form and symmetric tensor slots to mixed Young output" {
    const testing = std.testing;

    const spec: StructuralProjectorSpec = .{
        .operator_id = 9241,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
        },
        .right = .{
            .index = 2,
            .young_row_count = 1,
            .young_rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 2,
        },
        .output = .{
            .index = 3,
            .young_row_count = 2,
            .young_rows = .{ 3, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 4,
        },
    };

    const term_count = structuralProjectorTermCount(spec);
    try testing.expect(term_count != 0);
    const channel = try tensorCompilerChannelFromStructural(spec);
    try testing.expectEqual(TensorChannelKind.young_output, try tensorChannelKind(channel));
    const vector_spec = vectorSlotProjectorSpecFromChannel(channel).?;
    try testing.expectEqual(@as(u8, 2), vector_spec.left_slot_count);
    try testing.expectEqual(@as(u8, 2), vector_spec.right_slot_count);
    try testing.expectEqual(@as(u8, 4), vector_spec.shape.box_count);
    try testing.expectEqual(@as(u128, 1) << 4, vector_spec.left_form_profile);

    const tensor_program = try compileDiagnosticFallbackTensorChannelProgram(channel);
    try testing.expectEqual(CachedVectorProgramKind.projector, tensor_program.kind);
    try testing.expect(tensor_program.candidate_count != 0);
    try testing.expect(tensor_program.pivot_count != 0);
    try testing.expectEqual(TensorPrimitiveKind.form_bridge, tensor_program.words[0].primitives[0].kind);
    try testing.expectEqual(TensorPrimitiveKind.vector_young_output, tensor_program.words[0].primitives[1].kind);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var saw_form_exposure_delta = false;
    var saw_right_young_slot = false;
    var saw_output_young_slot = false;
    var saw_metric = false;
    var term_index: u16 = 0;
    while (term_index < term_count) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try appendStructuralProjectorTerm(testing.allocator, &atoms, spec, term_index);
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_delta => |delta| {
                    if (delta.upper == tensorFormRankBlock(spec.left.index, 2)) saw_form_exposure_delta = true;
                    if (delta.upper == spec.right.index) saw_right_young_slot = true;
                    if (delta.lower == spec.output.index) saw_output_young_slot = true;
                },
                .vector_slot_metric => |metric| {
                    saw_metric = true;
                    if (metric.left == tensorFormRankBlock(spec.left.index, 2) or metric.right == tensorFormRankBlock(spec.left.index, 2)) saw_form_exposure_delta = true;
                    if (metric.left == spec.right.index or metric.right == spec.right.index) saw_right_young_slot = true;
                    if (metric.left == spec.output.index or metric.right == spec.output.index) saw_output_young_slot = true;
                },
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
    try testing.expect(saw_form_exposure_delta);
    try testing.expect(saw_right_young_slot);
    try testing.expect(saw_output_young_slot);
    try testing.expect(saw_metric);
}

test "projector constructor pairs compressed form profiles through vector-slot backend" {
    const testing = std.testing;

    const profile = (@as(u128, 1) << 0) | (@as(u128, 1) << 4);
    const spec: StructuralProjectorSpec = .{
        .operator_id = 925,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = profile,
            .form_mask = 0b11,
            .form_count = 2,
        },
        .right = .{
            .index = 2,
            .form_profile = profile,
            .form_mask = 0b11,
            .form_count = 2,
        },
        .output = .{ .index = 3 },
    };

    const term_count = structuralProjectorTermCount(spec);
    try testing.expect(term_count != 0);
    const pairing_spec = tensorPairingSpecFromStructural(spec).?;
    try testing.expectEqual(profile, pairing_spec.left_form_profile);
    try testing.expectEqual(profile, pairing_spec.right_form_profile);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var saw_left_rank_one_block = false;
    var saw_left_rank_two_block = false;
    var saw_right_rank_one_block = false;
    var saw_right_rank_two_block = false;
    var term_index: u16 = 0;
    while (term_index < term_count) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try appendStructuralProjectorTerm(testing.allocator, &atoms, spec, term_index);
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_metric => |metric| {
                    if (metric.left == tensorFormRankBlock(spec.left.index, 1) or metric.right == tensorFormRankBlock(spec.left.index, 1)) saw_left_rank_one_block = true;
                    if (metric.left == tensorFormRankBlock(spec.left.index, 2) or metric.right == tensorFormRankBlock(spec.left.index, 2)) saw_left_rank_two_block = true;
                    if (metric.left == tensorFormRankBlock(spec.right.index, 1) or metric.right == tensorFormRankBlock(spec.right.index, 1)) saw_right_rank_one_block = true;
                    if (metric.left == tensorFormRankBlock(spec.right.index, 2) or metric.right == tensorFormRankBlock(spec.right.index, 2)) saw_right_rank_two_block = true;
                },
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
    try testing.expect(saw_left_rank_one_block);
    try testing.expect(saw_left_rank_two_block);
    try testing.expect(saw_right_rank_one_block);
    try testing.expect(saw_right_rank_two_block);
}

test "projector constructor streams vector two-form hook terms" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 93,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = 1,
            .form_mask = 1,
            .form_count = 1,
            .form_rank = 1,
        },
        .right = .{
            .index = 2,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
        },
        .output = .{
            .index = 3,
            .young_row_count = 2,
            .young_rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
    };

    const term_count = structuralProjectorTermCount(spec);
    try testing.expect(term_count >= 5);
    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var delta_count: u32 = 0;
    var metric_count: u32 = 0;
    var term_index: u8 = 0;
    while (term_index < term_count) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try appendStructuralProjectorTerm(testing.allocator, &atoms, spec, term_index);
        try testing.expectEqual(@as(usize, 6), atoms.items.len);
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_delta => delta_count += 1,
                .vector_slot_metric => metric_count += 1,
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
    try testing.expect(delta_count != 0);
    try testing.expect(metric_count != 0);
}

test "projector constructor vector two-form hook projector laws hold exactly" {
    const testing = std.testing;

    var input = hookTestZeroTensor();
    var a: usize = 0;
    while (a < hook_test_dimension) : (a += 1) {
        var b: usize = 0;
        while (b < hook_test_dimension) : (b += 1) {
            var c = b + 1;
            while (c < hook_test_dimension) : (c += 1) {
                const value = try Rational.init(@intCast((a + 1) * 7 + (b + 1) * 3 - (c + 1) * 2), 1);
                input[a][b][c] = value;
                input[a][c][b] = try Rational.zero().sub(value);
            }
        }
    }

    const projected = try hookTestApply(&input);
    const projected_twice = try hookTestApply(&projected);
    a = 0;
    while (a < hook_test_dimension) : (a += 1) {
        var b: usize = 0;
        while (b < hook_test_dimension) : (b += 1) {
            var c: usize = 0;
            while (c < hook_test_dimension) : (c += 1) {
                try testing.expect(rationalValueEql(projected[a][b][c], projected_twice[a][b][c]));

                const antisymmetry = try projected[a][b][c].add(projected[a][c][b]);
                try expectHookTestZero(antisymmetry);
                const cyclic = try (try projected[a][b][c].add(projected[b][c][a])).add(projected[c][a][b]);
                try expectHookTestZero(cyclic);
            }
        }
        var trace_index: usize = 0;
        while (trace_index < hook_test_dimension) : (trace_index += 1) {
            try expectHookTestZero(try hookTestTrace(&projected, trace_index));
        }
    }
}

test "projector constructor streams two-form square Weyl Young terms through Brauer program" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 94,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
        },
        .right = .{
            .index = 2,
            .form_profile = @as(u128, 1) << 4,
            .form_mask = @as(u64, 1) << 1,
            .form_count = 1,
            .form_rank = 2,
        },
        .output = .{
            .index = 3,
            .young_row_count = 2,
            .young_rows = .{ 2, 2, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 4,
        },
    };
    const vector_spec = vectorSlotProjectorSpecFromStructural(spec).?;
    const program = try compileVectorYoungBrauerProgram(vector_spec);
    try testing.expect(program.candidate_count < 12);
    try testing.expect(program.candidates[program.pivots[0]].word_count > 1);
    try testing.expect(program.pivot_count != 0);
    try testing.expect(program.pivot_count <= program.candidate_count);
    var saw_off_diagonal_inverse = false;
    var inverse_row: u8 = 0;
    while (inverse_row < program.pivot_count) : (inverse_row += 1) {
        var inverse_column: u8 = 0;
        while (inverse_column < program.pivot_count) : (inverse_column += 1) {
            if (inverse_row != inverse_column and program.inverse_gram[@as(usize, inverse_row) * program.pivot_count + inverse_column].numerator != 0) saw_off_diagonal_inverse = true;
        }
    }
    try testing.expect(saw_off_diagonal_inverse);
    try testing.expect(program.term_count >= 42);
    const tensor_program = try compileDiagnosticFallbackTensorChannelProgram(try tensorCompilerChannelFromStructural(spec));
    try testing.expect(tensor_program.term_count > program.term_count);
    try testing.expectEqual(tensor_program.term_count, structuralProjectorTermCount(spec));

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var term_index: u16 = 0;
    while (term_index < tensor_program.term_count and term_index < 64) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        _ = try appendStructuralProjectorTerm(testing.allocator, &atoms, spec, term_index);
        try testing.expectEqual(@as(usize, 8), atoms.items.len);
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_delta => {},
                .vector_slot_metric => {},
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
}

test "projector constructor removes dependent tensor candidate words by exact Gram" {
    const testing = std.testing;
    const spec: VectorSlotProjectorSpec = .{
        .operator_id = 941,
        .dimension = 10,
        .left = 1,
        .left_slot_count = 1,
        .right = 2,
        .right_slot_count = 1,
        .output = 3,
        .shape = .{ .row_count = 1, .rows = .{ 2, 0, 0, 0, 0, 0, 0, 0 }, .box_count = 2 },
    };

    var program = try initVectorBackedTensorChannelProgram(.projector, spec);
    var first: TensorCandidateWord = .{};
    try first.append(.{ .kind = .vector_young_output, .candidate_index = 0 });
    var second: TensorCandidateWord = .{};
    try second.append(.{ .kind = .vector_young_output, .candidate_index = 0 });

    program.candidate_count = 2;
    program.words[0] = first;
    program.words[1] = second;
    try compileTensorWordGram(&program);

    try testing.expect(program.candidate_count > program.pivot_count);
    try testing.expectEqual(@as(u8, 1), program.pivot_count);
    try testing.expectEqual(@as(u8, 0), program.pivots[0]);
    try testing.expect(program.pivot_count != 0);
    program.term_count = try countTensorChannelProgramTerms(program);
    try testing.expect(program.term_count != 0);
}

test "projector constructor Weyl Brauer program satisfies rank-4 laws exactly" {
    const testing = std.testing;
    const spec: VectorSlotProjectorSpec = .{
        .operator_id = 95,
        .dimension = hook_test_dimension,
        .left = 1,
        .left_slot_count = 2,
        .right = 2,
        .right_slot_count = 2,
        .output = 3,
        .shape = .{ .row_count = 2, .rows = .{ 2, 2, 0, 0, 0, 0, 0, 0 }, .box_count = 4 },
    };
    const program = try compileVectorYoungBrauerProgram(spec);

    var input = weylTestZeroTensor();
    var a: usize = 0;
    while (a < hook_test_dimension) : (a += 1) {
        var b = a + 1;
        while (b < hook_test_dimension) : (b += 1) {
            var c: usize = 0;
            while (c < hook_test_dimension) : (c += 1) {
                var d = c + 1;
                while (d < hook_test_dimension) : (d += 1) {
                    const signed_value: i64 = @as(i64, @intCast(a + 1)) * 11 - @as(i64, @intCast(b + 1)) * 5 + @as(i64, @intCast(c + 1)) * 3 - @as(i64, @intCast(d + 1));
                    const value = try Rational.init(signed_value, 1);
                    input[a][b][c][d] = value;
                    input[b][a][c][d] = try Rational.zero().sub(value);
                    input[a][b][d][c] = try Rational.zero().sub(value);
                    input[b][a][d][c] = value;
                }
            }
        }
    }

    const projected = try weylProgramApply(spec, program, &input);
    const projected_twice = try weylProgramApply(spec, program, &projected);
    a = 0;
    while (a < hook_test_dimension) : (a += 1) {
        var b: usize = 0;
        while (b < hook_test_dimension) : (b += 1) {
            var c: usize = 0;
            while (c < hook_test_dimension) : (c += 1) {
                var d: usize = 0;
                while (d < hook_test_dimension) : (d += 1) {
                    try testing.expect(rationalValueEql(projected[a][b][c][d], projected_twice[a][b][c][d]));
                    try expectHookTestZero(try projected[a][b][c][d].add(projected[b][a][c][d]));
                    try expectHookTestZero(try projected[a][b][c][d].add(projected[a][b][d][c]));
                    try testing.expect(rationalValueEql(projected[a][b][c][d], projected[c][d][a][b]));
                    const bianchi = try (try projected[a][b][c][d].add(projected[a][c][d][b])).add(projected[a][d][b][c]);
                    try expectHookTestZero(bianchi);
                }
            }
        }
    }
    var trace_b: usize = 0;
    while (trace_b < hook_test_dimension) : (trace_b += 1) {
        var d: usize = 0;
        while (d < hook_test_dimension) : (d += 1) {
            try expectHookTestZero(try weylTestTrace(&projected, trace_b, d));
        }
    }
}

test "projector constructor Weyl Brauer program is dimension-parametric outside D5" {
    const testing = std.testing;
    const spec: VectorSlotProjectorSpec = .{
        .operator_id = 96,
        .dimension = 9,
        .left = 1,
        .left_slot_count = 2,
        .right = 2,
        .right_slot_count = 2,
        .output = 3,
        .shape = .{ .row_count = 2, .rows = .{ 2, 2, 0, 0, 0, 0, 0, 0 }, .box_count = 4 },
    };
    const program = try compileVectorYoungBrauerProgram(spec);
    try testing.expect(program.candidate_count < 12);
    try testing.expect(program.pivot_count != 0);
    try testing.expect(program.pivot_count <= program.candidate_count);
    var saw_dimension_nine_trace = false;
    var term_index: u8 = 0;
    while (term_index < program.term_count) : (term_index += 1) {
        const coefficient = program.terms[term_index].coefficient;
        if (@mod(coefficient.denominator, 7) == 0) saw_dimension_nine_trace = true;
    }
    try testing.expect(saw_dimension_nine_trace);
}

test "projector constructor streams B4 Weyl scalar pairings through Brauer backend" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 97,
        .orthogonal_dimension = 9,
        .left = .{
            .index = 1,
            .young_row_count = 2,
            .young_rows = .{ 2, 2, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 4,
        },
        .right = .{
            .index = 2,
            .young_row_count = 2,
            .young_rows = .{ 2, 2, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 4,
        },
        .output = .{ .index = 3 },
    };
    const pairing_spec = tensorPairingSpecFromStructural(spec).?;
    const vector_spec = vectorProjectorSpecForPairing(pairing_spec);
    const program = try compileVectorYoungBrauerProgram(vector_spec);
    const term_count = structuralProjectorTermCount(spec);
    try testing.expect(term_count > program.term_count);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var term_index: u16 = 0;
    while (term_index < term_count and term_index < 64) : (term_index += 1) {
        atoms.clearRetainingCapacity();
        const coefficient = try appendStructuralProjectorTerm(testing.allocator, &atoms, spec, term_index);
        try testing.expectEqual(@as(usize, 8), atoms.items.len);
        _ = coefficient;
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_metric => {},
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
}

test "projector constructor streams D6 nonfixture Young scalar pairings through tensor candidates" {
    const testing = std.testing;
    const d6: symmetry.SimpleLieAlgebra = .{ .family = .d, .rank = 6 };
    const descriptor = try orthogonalTensorDescriptorFromDynkin(d6, &.{ 2, 1, 0, 0, 0, 0 });
    try testing.expectEqual(OrthogonalTensorKind.vector_young, descriptor.kind);
    try testing.expectEqual(@as(u16, 12), descriptor.dimension);
    try expectDescriptorRows(descriptor, &.{ 3, 1 });

    const spec: StructuralProjectorSpec = .{
        .operator_id = 971,
        .orthogonal_dimension = descriptor.dimension,
        .left = .{
            .index = 1,
            .young_row_count = descriptor.young_row_count,
            .young_rows = descriptor.young_rows,
            .young_box_count = descriptor.young_box_count,
        },
        .right = .{
            .index = 2,
            .young_row_count = descriptor.young_row_count,
            .young_rows = descriptor.young_rows,
            .young_box_count = descriptor.young_box_count,
        },
        .output = .{ .index = 3 },
    };

    const channel = try tensorCompilerChannelFromStructural(spec);
    try testing.expectEqual(TensorChannelKind.scalar_pairing, try tensorChannelKind(channel));
    const program = try compileDiagnosticFallbackTensorChannelProgram(channel);
    try testing.expectEqual(CachedVectorProgramKind.pairing, program.kind);
    try testing.expect(program.candidate_count != 0);
    try testing.expect(program.pivot_count != 0);
    try testing.expect(program.pivot_count <= program.candidate_count);
    try testing.expect(program.term_count != 0);
    try testing.expectEqual(program.term_count, structuralProjectorTermCount(spec));
    try testing.expectEqual(TensorPrimitiveKind.vector_young_pairing, program.words[0].primitives[0].kind);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var sample_index: u8 = 0;
    while (sample_index < 3) : (sample_index += 1) {
        const term_index = switch (sample_index) {
            0 => 0,
            1 => program.term_count / 2,
            else => program.term_count - 1,
        };
        atoms.clearRetainingCapacity();
        _ = try appendStructuralProjectorTerm(testing.allocator, &atoms, spec, term_index);
        try testing.expectEqual(@as(usize, 8), atoms.items.len);
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_metric => {},
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
}

test "projector constructor streams beyond-four-box exterior scalar pairings" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 98,
        .orthogonal_dimension = 9,
        .left = .{
            .index = 1,
            .young_row_count = 5,
            .young_rows = .{ 1, 1, 1, 1, 1, 0, 0, 0 },
            .young_box_count = 5,
        },
        .right = .{
            .index = 2,
            .young_row_count = 5,
            .young_rows = .{ 1, 1, 1, 1, 1, 0, 0, 0 },
            .young_box_count = 5,
        },
        .output = .{ .index = 3 },
    };
    try testing.expect(tensorPairingSpecFromStructural(spec) != null);
    const term_count = structuralProjectorTermCount(spec);
    try testing.expect(term_count != 0);

    var atoms: std.ArrayList(rendering.SymbolicAtom) = .empty;
    defer atoms.deinit(testing.allocator);
    var sample_index: u8 = 0;
    while (sample_index < 3) : (sample_index += 1) {
        const term_index = switch (sample_index) {
            0 => 0,
            1 => term_count / 2,
            else => term_count - 1,
        };
        atoms.clearRetainingCapacity();
        _ = try appendStructuralProjectorTerm(testing.allocator, &atoms, spec, term_index);
        try testing.expectEqual(@as(usize, 10), atoms.items.len);
        for (atoms.items) |atom| {
            switch (atom) {
                .vector_slot_metric => {},
                else => return error.ExpectedVectorSlotPrimitive,
            }
        }
    }
}

test "projector constructor rejects mismatched Young scalar pairings" {
    const testing = std.testing;
    const spec: StructuralProjectorSpec = .{
        .operator_id = 99,
        .orthogonal_dimension = 10,
        .left = .{
            .index = 1,
            .young_row_count = 2,
            .young_rows = .{ 2, 2, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 4,
        },
        .right = .{
            .index = 2,
            .young_row_count = 2,
            .young_rows = .{ 2, 1, 0, 0, 0, 0, 0, 0 },
            .young_box_count = 3,
        },
        .output = .{ .index = 3 },
    };
    try testing.expect(tensorPairingSpecFromStructural(spec) == null);
    try testing.expectEqual(@as(u16, 0), structuralProjectorTermCount(spec));
}
