// source-hash lisp/string-code-cft.asd 22ADEA4A
// source-hash lisp/string-code-cft-descriptor.lisp FAD306CF
// source-hash lisp/string-code-cft-presets.lisp B707C9FD
// source-hash lisp/presets/free-fermion-10.lisp AD507CFC
// source-hash lisp/presets/eta-xi.lisp 7841298B
// source-hash lisp/presets/bc-sphere.lisp 9DCE20B7
// source-hash lisp/presets/free-boson-10.lisp 2A73EFEE

const std = @import("std");
const descriptor = @import("descriptor.zig");

const d = descriptor;

fn cref(side: d.Side) d.CoordinateRef {
    return .{ .side = side, .slot = .position };
}

fn bulk(side: d.Side, slot: d.CoordinateSlot) d.CoordinateRef {
    return .{ .side = side, .slot = slot };
}

fn lref(side: d.Side, slot: d.Id) d.LabelRef {
    return .{ .side = side, .slot = slot };
}

const free_fermion_symbols = [_][]const u8{ "free-fermion-10", "spin10", "d5", "fermion-number", "psi", "mu", "vector", "free_fermion" };
const free_fermion_parameters = [_]d.Parameter{
};
const free_fermion_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 1, .kind = .ade_irrep, .group_symbol = 2 },
    .{ .id = 1, .symbol = 3, .kind = .zn_phase, .modulus = 2 },
};
const free_fermion_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .symbol = 6 } },
    .{ .field = 0, .quantum_number = 1, .value = .{ .integer = 1 } },
};
const free_fermion_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .sphere, .coordinate_model = .rational },
};
const free_fermion_fields = [_]d.Field{
    .{ .id = 0, .symbol = 4, .insertion = .single, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 5 }}, .statistics = .fermionic, .weight = 0, .infinity_behavior = .primary_from_weight },
};
const free_fermion_metadata = [_]d.MetadataExpr{
    .{ .rational = .{ .numerator = 1, .denominator = 2 } },
};
const free_fermion_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{} },
};
const free_fermion_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 0, .terms = &free_fermion_terms_0 },
};
const free_fermion_zero_modes = [_]d.ZeroModeRule{
};
const free_fermion_basis_oscillator_delta_0 = [_]i32{ 1 };
const free_fermion_basis_oscillators = [_]d.BasisOscillatorFamily{
    .{ .field = 0, .statistics = .fermionic, .first_tick = 1, .step_tick = 2, .base_weight_ticks = 1, .derivative_step_ticks = 2, .multiplicity = 10, .quantum_delta = &free_fermion_basis_oscillator_delta_0 },
};
const free_fermion_basis_seeds = [_]d.BasisSeedFamily{
};
const free_fermion_basis_render_modes = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 4, .base_weight_ticks = 1, .derivative_step_ticks = 2 },
};
const free_fermion_basis_render_seed_bits = [_]d.BasisRenderAtom{
};
pub const free_fermion_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 2480407866,
    .kind_namespace = 7,
    .symbols = &free_fermion_symbols,
    .parameters = &free_fermion_parameters,
    .quantum_numbers = &free_fermion_quantum_numbers,
    .field_quantum_numbers = &free_fermion_field_quantum_numbers,
    .surfaces = &free_fermion_surfaces,
    .fields = &free_fermion_fields,
    .metadata = &free_fermion_metadata,
    .wick_rules = &free_fermion_wick,
    .zero_modes = &free_fermion_zero_modes,
    .basis = .{ .kind = .free_fermion, .dimension = 10, .tick_denominator = 2 },
    .basis_rule = .{ .oscillators = &free_fermion_basis_oscillators, .seed_families = &free_fermion_basis_seeds, .drop_empty_seed = false, .render_modes = &free_fermion_basis_render_modes, .render_seed_bits = &free_fermion_basis_render_seed_bits },
};

/// FreeFermion is the lowered generated preset.
pub const FreeFermion = d.GeneratedTheory(free_fermion_descriptor);

const eta_xi_sphere_symbols = [_][]const u8{ "eta-xi", "eta-xi-number", "eta", "xi", "eta_xi" };
const eta_xi_sphere_parameters = [_]d.Parameter{
};
const eta_xi_sphere_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 1, .kind = .u1_charge },
};
const eta_xi_sphere_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .integer = 1 } },
    .{ .field = 1, .quantum_number = 0, .value = .{ .integer = -1 } },
};
const eta_xi_sphere_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .sphere, .coordinate_model = .rational },
};
const eta_xi_sphere_fields = [_]d.Field{
    .{ .id = 0, .symbol = 2, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 1, .symbol = 3, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .zero_mode_consumable = true, .weight = 1, .infinity_behavior = .primary_from_weight },
};
const eta_xi_sphere_metadata = [_]d.MetadataExpr{
    .{ .rational = .{ .numerator = 1, .denominator = 1 } },
    .{ .rational = .{ .numerator = 0, .denominator = 1 } },
};
const eta_xi_sphere_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{}, .actions = &.{}, .residuals = &.{} },
};
const eta_xi_sphere_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 1, .terms = &eta_xi_sphere_terms_0 },
};
const eta_xi_sphere_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .selector = .{ .fields = &.{1}, .exact_count = 1 }, .saturation = .grassmann_count },
};
const eta_xi_sphere_basis_oscillator_delta_0 = [_]i32{ 1 };
const eta_xi_sphere_basis_oscillator_delta_1 = [_]i32{ -1 };
const eta_xi_sphere_basis_seed_delta_0 = [_]i32{ -1 };
const eta_xi_sphere_basis_oscillators = [_]d.BasisOscillatorFamily{
    .{ .field = 0, .statistics = .fermionic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = 1, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &eta_xi_sphere_basis_oscillator_delta_0 },
    .{ .field = 1, .statistics = .fermionic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = 0, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &eta_xi_sphere_basis_oscillator_delta_1 },
};
const eta_xi_sphere_basis_seeds = [_]d.BasisSeedFamily{
    .{ .field = 1, .statistics = .fermionic, .first_weight_ticks = 0, .step_tick = 1, .last_weight_ticks = 0, .multiplicity = 1, .quantum_delta = &eta_xi_sphere_basis_seed_delta_0 },
};
const eta_xi_sphere_basis_render_modes = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 2, .base_weight_ticks = 1, .derivative_step_ticks = 1, .show_label = false },
    .{ .id = 1, .name_symbol = 3, .base_weight_ticks = 0, .derivative_step_ticks = 1, .show_label = false },
};
const eta_xi_sphere_basis_render_seed_bits = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 3, .base_weight_ticks = 0, .derivative_step_ticks = 1, .fixed_weight_ticks = 0, .show_label = false },
};
pub const eta_xi_sphere_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 542627842,
    .kind_namespace = 4,
    .symbols = &eta_xi_sphere_symbols,
    .parameters = &eta_xi_sphere_parameters,
    .quantum_numbers = &eta_xi_sphere_quantum_numbers,
    .field_quantum_numbers = &eta_xi_sphere_field_quantum_numbers,
    .surfaces = &eta_xi_sphere_surfaces,
    .fields = &eta_xi_sphere_fields,
    .metadata = &eta_xi_sphere_metadata,
    .wick_rules = &eta_xi_sphere_wick,
    .zero_modes = &eta_xi_sphere_zero_modes,
    .basis = .{ .kind = .eta_xi, .tick_denominator = 1 },
    .basis_rule = .{ .oscillators = &eta_xi_sphere_basis_oscillators, .seed_families = &eta_xi_sphere_basis_seeds, .drop_empty_seed = false, .render_modes = &eta_xi_sphere_basis_render_modes, .render_seed_bits = &eta_xi_sphere_basis_render_seed_bits },
};

/// EtaXiSphere is the lowered generated preset.
pub const EtaXiSphere = d.GeneratedTheory(eta_xi_sphere_descriptor);

const eta_xi_torus_symbols = [_][]const u8{ "eta-xi", "tau", "eta-xi-number", "eta", "xi", "eta_xi", "elliptic_prime_form_log_derivative" };
const eta_xi_torus_parameters = [_]d.Parameter{
    .{ .id = 0, .symbol = 1, .role = .modular_parameter },
};
const eta_xi_torus_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 2, .kind = .u1_charge },
};
const eta_xi_torus_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .integer = 1 } },
    .{ .field = 1, .quantum_number = 0, .value = .{ .integer = -1 } },
};
const eta_xi_torus_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .torus, .coordinate_model = .elliptic, .modular_parameter = 0 },
};
const eta_xi_torus_fields = [_]d.Field{
    .{ .id = 0, .symbol = 3, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 1, .symbol = 4, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .zero_mode_consumable = true, .weight = 1, .infinity_behavior = .primary_from_weight },
};
const eta_xi_torus_metadata = [_]d.MetadataExpr{
    .{ .rational = .{ .numerator = 1, .denominator = 1 } },
    .{ .rational = .{ .numerator = 0, .denominator = 1 } },
};
const eta_xi_torus_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .named_kernel = .{ .symbol = 6, .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .derive_left = true } }}, .tensors = &.{}, .actions = &.{}, .residuals = &.{} },
};
const eta_xi_torus_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 1, .terms = &eta_xi_torus_terms_0 },
};
const eta_xi_torus_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .selector = .{ .fields = &.{1}, .exact_count = 1 }, .saturation = .grassmann_count },
};
const eta_xi_torus_basis_oscillator_delta_0 = [_]i32{ 1 };
const eta_xi_torus_basis_oscillator_delta_1 = [_]i32{ -1 };
const eta_xi_torus_basis_seed_delta_0 = [_]i32{ -1 };
const eta_xi_torus_basis_oscillators = [_]d.BasisOscillatorFamily{
    .{ .field = 0, .statistics = .fermionic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = 1, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &eta_xi_torus_basis_oscillator_delta_0 },
    .{ .field = 1, .statistics = .fermionic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = 0, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &eta_xi_torus_basis_oscillator_delta_1 },
};
const eta_xi_torus_basis_seeds = [_]d.BasisSeedFamily{
    .{ .field = 1, .statistics = .fermionic, .first_weight_ticks = 0, .step_tick = 1, .last_weight_ticks = 0, .multiplicity = 1, .quantum_delta = &eta_xi_torus_basis_seed_delta_0 },
};
const eta_xi_torus_basis_render_modes = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 3, .base_weight_ticks = 1, .derivative_step_ticks = 1, .show_label = false },
    .{ .id = 1, .name_symbol = 4, .base_weight_ticks = 0, .derivative_step_ticks = 1, .show_label = false },
};
const eta_xi_torus_basis_render_seed_bits = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 4, .base_weight_ticks = 0, .derivative_step_ticks = 1, .fixed_weight_ticks = 0, .show_label = false },
};
pub const eta_xi_torus_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 1037149120,
    .kind_namespace = 5,
    .symbols = &eta_xi_torus_symbols,
    .parameters = &eta_xi_torus_parameters,
    .quantum_numbers = &eta_xi_torus_quantum_numbers,
    .field_quantum_numbers = &eta_xi_torus_field_quantum_numbers,
    .surfaces = &eta_xi_torus_surfaces,
    .fields = &eta_xi_torus_fields,
    .metadata = &eta_xi_torus_metadata,
    .wick_rules = &eta_xi_torus_wick,
    .zero_modes = &eta_xi_torus_zero_modes,
    .basis = .{ .kind = .eta_xi, .tick_denominator = 1 },
    .basis_rule = .{ .oscillators = &eta_xi_torus_basis_oscillators, .seed_families = &eta_xi_torus_basis_seeds, .drop_empty_seed = false, .render_modes = &eta_xi_torus_basis_render_modes, .render_seed_bits = &eta_xi_torus_basis_render_seed_bits },
};

/// EtaXiTorus is the lowered generated preset.
pub const EtaXiTorus = d.GeneratedTheory(eta_xi_torus_descriptor);

const bc_symbols = [_][]const u8{ "bc", "ghost-number", "b", "c" };
const bc_parameters = [_]d.Parameter{
};
const bc_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 1, .kind = .u1_charge },
};
const bc_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .integer = -1 } },
    .{ .field = 1, .quantum_number = 0, .value = .{ .integer = 1 } },
};
const bc_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .sphere, .coordinate_model = .rational },
};
const bc_fields = [_]d.Field{
    .{ .id = 0, .symbol = 2, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 1, .symbol = 3, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .zero_mode_consumable = true, .weight = 1, .infinity_behavior = .primary_from_weight },
};
const bc_metadata = [_]d.MetadataExpr{
    .{ .rational = .{ .numerator = 2, .denominator = 1 } },
    .{ .rational = .{ .numerator = -1, .denominator = 1 } },
};
const bc_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{}, .actions = &.{}, .residuals = &.{} },
};
const bc_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 1, .terms = &bc_terms_0 },
};
const bc_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .selector = .{ .fields = &.{1}, .exact_count = 3, .allow_derivatives = true, .allow_infinity = true }, .saturation = .grassmann_top_form },
};
const bc_basis_oscillator_delta_0 = [_]i32{ -1 };
const bc_basis_oscillator_delta_1 = [_]i32{ -1 };
const bc_basis_seed_delta_0 = [_]i32{ 1 };
const bc_basis_oscillators = [_]d.BasisOscillatorFamily{
    .{ .field = 0, .statistics = .fermionic, .first_tick = 2, .step_tick = 1, .base_weight_ticks = 2, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &bc_basis_oscillator_delta_0 },
    .{ .field = 1, .statistics = .fermionic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = -1, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &bc_basis_oscillator_delta_1 },
};
const bc_basis_seeds = [_]d.BasisSeedFamily{
    .{ .field = 1, .statistics = .fermionic, .first_weight_ticks = -1, .step_tick = 1, .last_weight_ticks = 0, .multiplicity = 1, .quantum_delta = &bc_basis_seed_delta_0 },
};
const bc_basis_render_modes = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 2, .base_weight_ticks = 2, .derivative_step_ticks = 1, .show_label = false },
    .{ .id = 1, .name_symbol = 3, .base_weight_ticks = -1, .derivative_step_ticks = 1, .show_label = false },
};
const bc_basis_render_seed_bits = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 3, .base_weight_ticks = -1, .derivative_step_ticks = 1, .fixed_weight_ticks = -1, .show_label = false },
    .{ .id = 1, .name_symbol = 3, .base_weight_ticks = -1, .derivative_step_ticks = 1, .fixed_weight_ticks = 0, .show_label = false },
};
pub const bc_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 3697840228,
    .kind_namespace = 0,
    .symbols = &bc_symbols,
    .parameters = &bc_parameters,
    .quantum_numbers = &bc_quantum_numbers,
    .field_quantum_numbers = &bc_field_quantum_numbers,
    .surfaces = &bc_surfaces,
    .fields = &bc_fields,
    .metadata = &bc_metadata,
    .wick_rules = &bc_wick,
    .zero_modes = &bc_zero_modes,
    .basis = .{ .kind = .bc, .tick_denominator = 1 },
    .basis_rule = .{ .oscillators = &bc_basis_oscillators, .seed_families = &bc_basis_seeds, .drop_empty_seed = true, .render_modes = &bc_basis_render_modes, .render_seed_bits = &bc_basis_render_seed_bits },
};

/// Bc is the lowered generated preset.
pub const Bc = d.GeneratedTheory(bc_descriptor);

const free_boson_symbols = [_][]const u8{ "free-boson-10", "alpha-prime", "spin10", "d5", "X", "x", "mu", "vector", "dX", "d_x", "dXt", "d_xt", "eta", "expX", "exp_x", "k", "profile", "profile_x", "f", "pi", "free_boson" };
const free_boson_parameters = [_]d.Parameter{
    .{ .id = 0, .symbol = 1, .role = .scalar_parameter },
};
const free_boson_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 2, .kind = .ade_irrep, .group_symbol = 3 },
};
const free_boson_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .symbol = 7 } },
    .{ .field = 1, .quantum_number = 0, .value = .{ .symbol = 7 } },
    .{ .field = 2, .quantum_number = 0, .value = .{ .symbol = 7 } },
};
const free_boson_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .sphere, .coordinate_model = .rational },
};
const free_boson_fields = [_]d.Field{
    .{ .id = 0, .symbol = 4, .kind_symbol = 5, .insertion = .pair, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 6 }}, .statistics = .bosonic },
    .{ .id = 1, .symbol = 8, .kind_symbol = 9, .insertion = .single, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 6 }}, .statistics = .bosonic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 2, .symbol = 10, .kind_symbol = 11, .insertion = .single, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 6 }}, .statistics = .bosonic, .support = .antiholomorphic, .anti_weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 3, .symbol = 13, .kind_symbol = 14, .insertion = .pair, .labels = &.{.{ .id = 0, .role = .momentum, .symbol = 15 }}, .statistics = .bosonic, .zero_mode_consumable = true, .weight = 4, .anti_weight = 4, .infinity_behavior = .branch_global_exponential, .infinity_label = 0 },
    .{ .id = 4, .symbol = 16, .kind_symbol = 17, .insertion = .pair, .labels = &.{.{ .id = 0, .role = .profile, .symbol = 18 }}, .statistics = .bosonic, .zero_mode_consumable = true },
};
const free_boson_metadata = [_]d.MetadataExpr{
    .{ .rational = .{ .numerator = 1, .denominator = 1 } },
    .{ .field_label = .{ .field = 3, .label = 0 } },
    .{ .bilinear = .{ .left = 1, .right = 1, .form_symbol = 12 } },
    .{ .scalar_monomial = .{ .rational = .{ .numerator = 1, .denominator = 4 }, .imaginary_power = 0, .atom = 1, .atom_power = 1 } },
    .{ .mul = .{ .left = 3, .right = 2 } },
};
const free_boson_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = -1, .denominator = 2 }, .imaginary_power = 0, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -2, .derive_left = true, .derive_right = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{} },
};
const free_boson_terms_1 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = -1, .denominator = 2 }, .imaginary_power = 0, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -2, .derive_left = true, .derive_right = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{} },
};
const free_boson_terms_2 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = -1, .denominator = 2 }, .imaginary_power = 0, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .logarithm = .{ .left = .{ .side = .left, .slot = .holomorphic }, .right = .{ .side = .right, .slot = .holomorphic } } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{} },
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = -1, .denominator = 2 }, .imaginary_power = 0, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .logarithm = .{ .left = .{ .side = .left, .slot = .antiholomorphic }, .right = .{ .side = .right, .slot = .antiholomorphic } } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{} },
};
const free_boson_terms_3 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = -1, .denominator = 2 }, .imaginary_power = 0, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .logarithm = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .holomorphic }, .derive_left = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{} },
};
const free_boson_terms_4 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = -1, .denominator = 2 }, .imaginary_power = 0, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .logarithm = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .antiholomorphic }, .derive_left = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{} },
};
const free_boson_terms_5 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = -1, .denominator = 2 }, .imaginary_power = 1, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .holomorphic }, .exponent = -1, .derive_left = true } }}, .tensors = &.{.{ .momentum_index = .{ .momentum = .{ .side = .right, .slot = 0 }, .index = .{ .side = .left, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{.right} },
};
const free_boson_terms_6 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = -1, .denominator = 2 }, .imaginary_power = 1, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .antiholomorphic }, .exponent = -1, .derive_left = true } }}, .tensors = &.{.{ .momentum_index = .{ .momentum = .{ .side = .right, .slot = 0 }, .index = .{ .side = .left, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{.right} },
};
const free_boson_terms_7 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = -1, .denominator = 2 }, .imaginary_power = 0, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .holomorphic }, .exponent = -1, .derive_left = true } }}, .tensors = &.{}, .actions = &.{.{ .profile_derivative = .{ .profile = .{ .side = .right, .slot = 0 }, .index = .{ .side = .left, .slot = 0 } } }}, .residuals = &.{.right} },
};
const free_boson_terms_8 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = -1, .denominator = 2 }, .imaginary_power = 0, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .antiholomorphic }, .exponent = -1, .derive_left = true } }}, .tensors = &.{}, .actions = &.{.{ .profile_derivative = .{ .profile = .{ .side = .right, .slot = 0 }, .index = .{ .side = .left, .slot = 0 } } }}, .residuals = &.{.right} },
};
const free_boson_terms_9 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .monomial = .{ .rational = .{ .numerator = 1, .denominator = 2 }, .imaginary_power = 0, .atom = 1, .atom_power = 1 } }}, .coordinates = &.{.{ .green_exponential = .{ .left = .{ .side = .left, .slot = .holomorphic }, .right = .{ .side = .right, .slot = .holomorphic } } }, .{ .green_exponential = .{ .left = .{ .side = .left, .slot = .antiholomorphic }, .right = .{ .side = .right, .slot = .antiholomorphic } } }}, .tensors = &.{.{ .momentum_pair = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{.left, .right} },
};
const free_boson_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 1, .right = 1, .terms = &free_boson_terms_0 },
    .{ .surface = 0, .left = 2, .right = 2, .terms = &free_boson_terms_1 },
    .{ .surface = 0, .left = 0, .right = 0, .terms = &free_boson_terms_2 },
    .{ .surface = 0, .left = 1, .right = 0, .terms = &free_boson_terms_3 },
    .{ .surface = 0, .left = 2, .right = 0, .terms = &free_boson_terms_4 },
    .{ .surface = 0, .left = 1, .right = 3, .terms = &free_boson_terms_5 },
    .{ .surface = 0, .left = 2, .right = 3, .terms = &free_boson_terms_6 },
    .{ .surface = 0, .left = 1, .right = 4, .terms = &free_boson_terms_7 },
    .{ .surface = 0, .left = 2, .right = 4, .terms = &free_boson_terms_8 },
    .{ .surface = 0, .left = 3, .right = 3, .terms = &free_boson_terms_9 },
};
const free_boson_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .selector = .{ .fields = &.{3, 4}, .exact_count = 0, .allow_infinity = true }, .saturation = .linear_conservation, .normalization = .{ .monomial = .{ .rational = .{ .numerator = 1024, .denominator = 1 }, .imaginary_power = 0, .atom = 19, .atom_power = 10 } } },
};
const free_boson_basis_oscillator_delta_0 = [_]i32{  };
const free_boson_basis_oscillators = [_]d.BasisOscillatorFamily{
    .{ .field = 1, .statistics = .bosonic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = 0, .derivative_step_ticks = 1, .multiplicity = 10, .quantum_delta = &free_boson_basis_oscillator_delta_0 },
};
const free_boson_basis_seeds = [_]d.BasisSeedFamily{
};
const free_boson_basis_render_modes = [_]d.BasisRenderAtom{
    .{ .id = 1, .name_symbol = 8, .base_weight_ticks = 0, .derivative_step_ticks = 1 },
};
const free_boson_basis_render_seed_bits = [_]d.BasisRenderAtom{
};
pub const free_boson_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 2450282531,
    .kind_namespace = 20,
    .symbols = &free_boson_symbols,
    .parameters = &free_boson_parameters,
    .quantum_numbers = &free_boson_quantum_numbers,
    .field_quantum_numbers = &free_boson_field_quantum_numbers,
    .surfaces = &free_boson_surfaces,
    .fields = &free_boson_fields,
    .metadata = &free_boson_metadata,
    .wick_rules = &free_boson_wick,
    .zero_modes = &free_boson_zero_modes,
    .basis = .{ .kind = .free_boson, .dimension = 10, .tick_denominator = 1 },
    .basis_rule = .{ .oscillators = &free_boson_basis_oscillators, .seed_families = &free_boson_basis_seeds, .drop_empty_seed = false, .render_modes = &free_boson_basis_render_modes, .render_seed_bits = &free_boson_basis_render_seed_bits },
};

/// FreeBoson is the lowered generated preset.
pub const FreeBoson = d.GeneratedTheory(free_boson_descriptor);

const free_fermion_10_full_symbols = [_][]const u8{ "free-fermion-10-full", "spin10", "d5", "fermion-number", "psi", "mu", "vector", "psit", "free_fermion" };
const free_fermion_10_full_parameters = [_]d.Parameter{
};
const free_fermion_10_full_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 1, .kind = .ade_irrep, .group_symbol = 2 },
    .{ .id = 1, .symbol = 3, .kind = .zn_phase, .modulus = 2 },
};
const free_fermion_10_full_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .symbol = 6 } },
    .{ .field = 0, .quantum_number = 1, .value = .{ .integer = 1 } },
    .{ .field = 1, .quantum_number = 0, .value = .{ .symbol = 6 } },
    .{ .field = 1, .quantum_number = 1, .value = .{ .integer = 1 } },
};
const free_fermion_10_full_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .sphere, .coordinate_model = .rational },
};
const free_fermion_10_full_fields = [_]d.Field{
    .{ .id = 0, .symbol = 4, .insertion = .single, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 5 }}, .statistics = .fermionic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 1, .symbol = 7, .insertion = .single, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 5 }}, .statistics = .fermionic, .support = .antiholomorphic, .weight = 0, .infinity_behavior = .primary_from_weight },
};
const free_fermion_10_full_metadata = [_]d.MetadataExpr{
    .{ .rational = .{ .numerator = 1, .denominator = 2 } },
};
const free_fermion_10_full_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{} },
};
const free_fermion_10_full_terms_1 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .actions = &.{}, .residuals = &.{} },
};
const free_fermion_10_full_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 0, .terms = &free_fermion_10_full_terms_0 },
    .{ .surface = 0, .left = 1, .right = 1, .terms = &free_fermion_10_full_terms_1 },
};
const free_fermion_10_full_zero_modes = [_]d.ZeroModeRule{
};
const free_fermion_10_full_basis_oscillator_delta_0 = [_]i32{ 1 };
const free_fermion_10_full_basis_oscillators = [_]d.BasisOscillatorFamily{
    .{ .field = 0, .statistics = .fermionic, .first_tick = 1, .step_tick = 2, .base_weight_ticks = 1, .derivative_step_ticks = 2, .multiplicity = 10, .quantum_delta = &free_fermion_10_full_basis_oscillator_delta_0 },
};
const free_fermion_10_full_basis_seeds = [_]d.BasisSeedFamily{
};
const free_fermion_10_full_basis_render_modes = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 4, .base_weight_ticks = 1, .derivative_step_ticks = 2 },
};
const free_fermion_10_full_basis_render_seed_bits = [_]d.BasisRenderAtom{
};
pub const free_fermion_10_full_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 2291734364,
    .kind_namespace = 8,
    .symbols = &free_fermion_10_full_symbols,
    .parameters = &free_fermion_10_full_parameters,
    .quantum_numbers = &free_fermion_10_full_quantum_numbers,
    .field_quantum_numbers = &free_fermion_10_full_field_quantum_numbers,
    .surfaces = &free_fermion_10_full_surfaces,
    .fields = &free_fermion_10_full_fields,
    .metadata = &free_fermion_10_full_metadata,
    .wick_rules = &free_fermion_10_full_wick,
    .zero_modes = &free_fermion_10_full_zero_modes,
    .basis = .{ .kind = .free_fermion, .dimension = 10, .tick_denominator = 2 },
    .basis_rule = .{ .oscillators = &free_fermion_10_full_basis_oscillators, .seed_families = &free_fermion_10_full_basis_seeds, .drop_empty_seed = false, .render_modes = &free_fermion_10_full_basis_render_modes, .render_seed_bits = &free_fermion_10_full_basis_render_seed_bits },
};

/// FreeFermion10Full is the lowered generated preset.
pub const FreeFermion10Full = d.GeneratedTheory(free_fermion_10_full_descriptor);

const eta_xi_sphere_full_symbols = [_][]const u8{ "eta-xi-sphere-full", "eta-xi-number", "eta", "xi", "etat", "xit", "eta_xi" };
const eta_xi_sphere_full_parameters = [_]d.Parameter{
};
const eta_xi_sphere_full_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 1, .kind = .u1_charge },
};
const eta_xi_sphere_full_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .integer = 1 } },
    .{ .field = 1, .quantum_number = 0, .value = .{ .integer = -1 } },
    .{ .field = 2, .quantum_number = 0, .value = .{ .integer = 1 } },
    .{ .field = 3, .quantum_number = 0, .value = .{ .integer = -1 } },
};
const eta_xi_sphere_full_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .sphere, .coordinate_model = .rational },
};
const eta_xi_sphere_full_fields = [_]d.Field{
    .{ .id = 0, .symbol = 2, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 1, .symbol = 3, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .zero_mode_consumable = true, .weight = 1, .infinity_behavior = .primary_from_weight },
    .{ .id = 2, .symbol = 4, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .support = .antiholomorphic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 3, .symbol = 5, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .support = .antiholomorphic, .zero_mode_consumable = true, .weight = 1, .infinity_behavior = .primary_from_weight },
};
const eta_xi_sphere_full_metadata = [_]d.MetadataExpr{
    .{ .rational = .{ .numerator = 1, .denominator = 1 } },
    .{ .rational = .{ .numerator = 0, .denominator = 1 } },
};
const eta_xi_sphere_full_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{}, .actions = &.{}, .residuals = &.{} },
};
const eta_xi_sphere_full_terms_1 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{}, .actions = &.{}, .residuals = &.{} },
};
const eta_xi_sphere_full_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 1, .terms = &eta_xi_sphere_full_terms_0 },
    .{ .surface = 0, .left = 2, .right = 3, .terms = &eta_xi_sphere_full_terms_1 },
};
const eta_xi_sphere_full_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .selector = .{ .fields = &.{1}, .exact_count = 1 }, .saturation = .grassmann_count },
    .{ .surface = 0, .selector = .{ .fields = &.{3}, .exact_count = 1 }, .saturation = .grassmann_count },
};
const eta_xi_sphere_full_basis_oscillator_delta_0 = [_]i32{ 1 };
const eta_xi_sphere_full_basis_oscillator_delta_1 = [_]i32{ -1 };
const eta_xi_sphere_full_basis_seed_delta_0 = [_]i32{ -1 };
const eta_xi_sphere_full_basis_oscillators = [_]d.BasisOscillatorFamily{
    .{ .field = 0, .statistics = .fermionic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = 1, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &eta_xi_sphere_full_basis_oscillator_delta_0 },
    .{ .field = 1, .statistics = .fermionic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = 0, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &eta_xi_sphere_full_basis_oscillator_delta_1 },
};
const eta_xi_sphere_full_basis_seeds = [_]d.BasisSeedFamily{
    .{ .field = 1, .statistics = .fermionic, .first_weight_ticks = 0, .step_tick = 1, .last_weight_ticks = 0, .multiplicity = 1, .quantum_delta = &eta_xi_sphere_full_basis_seed_delta_0 },
};
const eta_xi_sphere_full_basis_render_modes = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 2, .base_weight_ticks = 1, .derivative_step_ticks = 1, .show_label = false },
    .{ .id = 1, .name_symbol = 3, .base_weight_ticks = 0, .derivative_step_ticks = 1, .show_label = false },
};
const eta_xi_sphere_full_basis_render_seed_bits = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 3, .base_weight_ticks = 0, .derivative_step_ticks = 1, .fixed_weight_ticks = 0, .show_label = false },
};
pub const eta_xi_sphere_full_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 1194179249,
    .kind_namespace = 6,
    .symbols = &eta_xi_sphere_full_symbols,
    .parameters = &eta_xi_sphere_full_parameters,
    .quantum_numbers = &eta_xi_sphere_full_quantum_numbers,
    .field_quantum_numbers = &eta_xi_sphere_full_field_quantum_numbers,
    .surfaces = &eta_xi_sphere_full_surfaces,
    .fields = &eta_xi_sphere_full_fields,
    .metadata = &eta_xi_sphere_full_metadata,
    .wick_rules = &eta_xi_sphere_full_wick,
    .zero_modes = &eta_xi_sphere_full_zero_modes,
    .basis = .{ .kind = .eta_xi, .tick_denominator = 1 },
    .basis_rule = .{ .oscillators = &eta_xi_sphere_full_basis_oscillators, .seed_families = &eta_xi_sphere_full_basis_seeds, .drop_empty_seed = false, .render_modes = &eta_xi_sphere_full_basis_render_modes, .render_seed_bits = &eta_xi_sphere_full_basis_render_seed_bits },
};

/// EtaXiSphereFull is the lowered generated preset.
pub const EtaXiSphereFull = d.GeneratedTheory(eta_xi_sphere_full_descriptor);

const eta_xi_torus_full_symbols = [_][]const u8{ "eta-xi-torus-full", "tau", "eta-xi-number", "eta", "xi", "etat", "xit", "eta_xi", "elliptic_prime_form_log_derivative" };
const eta_xi_torus_full_parameters = [_]d.Parameter{
    .{ .id = 0, .symbol = 1, .role = .modular_parameter },
};
const eta_xi_torus_full_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 2, .kind = .u1_charge },
};
const eta_xi_torus_full_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .integer = 1 } },
    .{ .field = 1, .quantum_number = 0, .value = .{ .integer = -1 } },
    .{ .field = 2, .quantum_number = 0, .value = .{ .integer = 1 } },
    .{ .field = 3, .quantum_number = 0, .value = .{ .integer = -1 } },
};
const eta_xi_torus_full_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .torus, .coordinate_model = .elliptic, .modular_parameter = 0 },
};
const eta_xi_torus_full_fields = [_]d.Field{
    .{ .id = 0, .symbol = 3, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 1, .symbol = 4, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .zero_mode_consumable = true, .weight = 1, .infinity_behavior = .primary_from_weight },
    .{ .id = 2, .symbol = 5, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .support = .antiholomorphic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 3, .symbol = 6, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .support = .antiholomorphic, .zero_mode_consumable = true, .weight = 1, .infinity_behavior = .primary_from_weight },
};
const eta_xi_torus_full_metadata = [_]d.MetadataExpr{
    .{ .rational = .{ .numerator = 1, .denominator = 1 } },
    .{ .rational = .{ .numerator = 0, .denominator = 1 } },
};
const eta_xi_torus_full_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .named_kernel = .{ .symbol = 8, .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .derive_left = true } }}, .tensors = &.{}, .actions = &.{}, .residuals = &.{} },
};
const eta_xi_torus_full_terms_1 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .named_kernel = .{ .symbol = 8, .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .derive_left = true } }}, .tensors = &.{}, .actions = &.{}, .residuals = &.{} },
};
const eta_xi_torus_full_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 1, .terms = &eta_xi_torus_full_terms_0 },
    .{ .surface = 0, .left = 2, .right = 3, .terms = &eta_xi_torus_full_terms_1 },
};
const eta_xi_torus_full_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .selector = .{ .fields = &.{1}, .exact_count = 1 }, .saturation = .grassmann_count },
    .{ .surface = 0, .selector = .{ .fields = &.{3}, .exact_count = 1 }, .saturation = .grassmann_count },
};
const eta_xi_torus_full_basis_oscillator_delta_0 = [_]i32{ 1 };
const eta_xi_torus_full_basis_oscillator_delta_1 = [_]i32{ -1 };
const eta_xi_torus_full_basis_seed_delta_0 = [_]i32{ -1 };
const eta_xi_torus_full_basis_oscillators = [_]d.BasisOscillatorFamily{
    .{ .field = 0, .statistics = .fermionic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = 1, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &eta_xi_torus_full_basis_oscillator_delta_0 },
    .{ .field = 1, .statistics = .fermionic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = 0, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &eta_xi_torus_full_basis_oscillator_delta_1 },
};
const eta_xi_torus_full_basis_seeds = [_]d.BasisSeedFamily{
    .{ .field = 1, .statistics = .fermionic, .first_weight_ticks = 0, .step_tick = 1, .last_weight_ticks = 0, .multiplicity = 1, .quantum_delta = &eta_xi_torus_full_basis_seed_delta_0 },
};
const eta_xi_torus_full_basis_render_modes = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 3, .base_weight_ticks = 1, .derivative_step_ticks = 1, .show_label = false },
    .{ .id = 1, .name_symbol = 4, .base_weight_ticks = 0, .derivative_step_ticks = 1, .show_label = false },
};
const eta_xi_torus_full_basis_render_seed_bits = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 4, .base_weight_ticks = 0, .derivative_step_ticks = 1, .fixed_weight_ticks = 0, .show_label = false },
};
pub const eta_xi_torus_full_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 2994057177,
    .kind_namespace = 7,
    .symbols = &eta_xi_torus_full_symbols,
    .parameters = &eta_xi_torus_full_parameters,
    .quantum_numbers = &eta_xi_torus_full_quantum_numbers,
    .field_quantum_numbers = &eta_xi_torus_full_field_quantum_numbers,
    .surfaces = &eta_xi_torus_full_surfaces,
    .fields = &eta_xi_torus_full_fields,
    .metadata = &eta_xi_torus_full_metadata,
    .wick_rules = &eta_xi_torus_full_wick,
    .zero_modes = &eta_xi_torus_full_zero_modes,
    .basis = .{ .kind = .eta_xi, .tick_denominator = 1 },
    .basis_rule = .{ .oscillators = &eta_xi_torus_full_basis_oscillators, .seed_families = &eta_xi_torus_full_basis_seeds, .drop_empty_seed = false, .render_modes = &eta_xi_torus_full_basis_render_modes, .render_seed_bits = &eta_xi_torus_full_basis_render_seed_bits },
};

/// EtaXiTorusFull is the lowered generated preset.
pub const EtaXiTorusFull = d.GeneratedTheory(eta_xi_torus_full_descriptor);

const bc_sphere_full_symbols = [_][]const u8{ "bc-sphere-full", "ghost-number", "b", "c", "bt", "ct", "bc" };
const bc_sphere_full_parameters = [_]d.Parameter{
};
const bc_sphere_full_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 1, .kind = .u1_charge },
};
const bc_sphere_full_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .integer = -1 } },
    .{ .field = 1, .quantum_number = 0, .value = .{ .integer = 1 } },
    .{ .field = 2, .quantum_number = 0, .value = .{ .integer = -1 } },
    .{ .field = 3, .quantum_number = 0, .value = .{ .integer = 1 } },
};
const bc_sphere_full_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .sphere, .coordinate_model = .rational },
};
const bc_sphere_full_fields = [_]d.Field{
    .{ .id = 0, .symbol = 2, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 1, .symbol = 3, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .zero_mode_consumable = true, .weight = 1, .infinity_behavior = .primary_from_weight },
    .{ .id = 2, .symbol = 4, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .support = .antiholomorphic, .weight = 0, .infinity_behavior = .primary_from_weight },
    .{ .id = 3, .symbol = 5, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .support = .antiholomorphic, .zero_mode_consumable = true, .weight = 1, .infinity_behavior = .primary_from_weight },
};
const bc_sphere_full_metadata = [_]d.MetadataExpr{
    .{ .rational = .{ .numerator = 2, .denominator = 1 } },
    .{ .rational = .{ .numerator = -1, .denominator = 1 } },
};
const bc_sphere_full_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{}, .actions = &.{}, .residuals = &.{} },
};
const bc_sphere_full_terms_1 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{}, .actions = &.{}, .residuals = &.{} },
};
const bc_sphere_full_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 1, .terms = &bc_sphere_full_terms_0 },
    .{ .surface = 0, .left = 2, .right = 3, .terms = &bc_sphere_full_terms_1 },
};
const bc_sphere_full_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .selector = .{ .fields = &.{1}, .exact_count = 3, .allow_derivatives = true, .allow_infinity = true }, .saturation = .grassmann_top_form },
    .{ .surface = 0, .selector = .{ .fields = &.{3}, .exact_count = 3, .allow_derivatives = true, .allow_infinity = true }, .saturation = .grassmann_top_form },
};
const bc_sphere_full_basis_oscillator_delta_0 = [_]i32{ -1 };
const bc_sphere_full_basis_oscillator_delta_1 = [_]i32{ -1 };
const bc_sphere_full_basis_seed_delta_0 = [_]i32{ 1 };
const bc_sphere_full_basis_oscillators = [_]d.BasisOscillatorFamily{
    .{ .field = 0, .statistics = .fermionic, .first_tick = 2, .step_tick = 1, .base_weight_ticks = 2, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &bc_sphere_full_basis_oscillator_delta_0 },
    .{ .field = 1, .statistics = .fermionic, .first_tick = 1, .step_tick = 1, .base_weight_ticks = -1, .derivative_step_ticks = 1, .multiplicity = 1, .quantum_delta = &bc_sphere_full_basis_oscillator_delta_1 },
};
const bc_sphere_full_basis_seeds = [_]d.BasisSeedFamily{
    .{ .field = 1, .statistics = .fermionic, .first_weight_ticks = -1, .step_tick = 1, .last_weight_ticks = 0, .multiplicity = 1, .quantum_delta = &bc_sphere_full_basis_seed_delta_0 },
};
const bc_sphere_full_basis_render_modes = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 2, .base_weight_ticks = 2, .derivative_step_ticks = 1, .show_label = false },
    .{ .id = 1, .name_symbol = 3, .base_weight_ticks = -1, .derivative_step_ticks = 1, .show_label = false },
};
const bc_sphere_full_basis_render_seed_bits = [_]d.BasisRenderAtom{
    .{ .id = 0, .name_symbol = 3, .base_weight_ticks = -1, .derivative_step_ticks = 1, .fixed_weight_ticks = -1, .show_label = false },
    .{ .id = 1, .name_symbol = 3, .base_weight_ticks = -1, .derivative_step_ticks = 1, .fixed_weight_ticks = 0, .show_label = false },
};
pub const bc_sphere_full_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 3993744863,
    .kind_namespace = 6,
    .symbols = &bc_sphere_full_symbols,
    .parameters = &bc_sphere_full_parameters,
    .quantum_numbers = &bc_sphere_full_quantum_numbers,
    .field_quantum_numbers = &bc_sphere_full_field_quantum_numbers,
    .surfaces = &bc_sphere_full_surfaces,
    .fields = &bc_sphere_full_fields,
    .metadata = &bc_sphere_full_metadata,
    .wick_rules = &bc_sphere_full_wick,
    .zero_modes = &bc_sphere_full_zero_modes,
    .basis = .{ .kind = .bc, .tick_denominator = 1 },
    .basis_rule = .{ .oscillators = &bc_sphere_full_basis_oscillators, .seed_families = &bc_sphere_full_basis_seeds, .drop_empty_seed = true, .render_modes = &bc_sphere_full_basis_render_modes, .render_seed_bits = &bc_sphere_full_basis_render_seed_bits },
};

/// BcSphereFull is the lowered generated preset.
pub const BcSphereFull = d.GeneratedTheory(bc_sphere_full_descriptor);

fn expectFieldInfinity(comptime desc: d.Descriptor, comptime field_id: d.Id, comptime behavior: d.InfinityBehavior, comptime support: d.FieldSupport, comptime weight: ?d.Id, comptime anti_weight: ?d.Id, comptime label: ?d.Id) !void {
    const field = desc.fields[field_id];
    try std.testing.expectEqual(behavior, field.infinity_behavior);
    try std.testing.expectEqual(support, field.support);
    try std.testing.expectEqual(weight, field.weight);
    try std.testing.expectEqual(anti_weight, field.anti_weight);
    try std.testing.expectEqual(label, field.infinity_label);
}

fn expectRationalMetadata(comptime desc: d.Descriptor, comptime id: d.Id, comptime numerator: i64, comptime denominator: i64) !void {
    switch (desc.metadata[id]) {
        .rational => |value| {
            try std.testing.expectEqual(numerator, value.numerator);
            try std.testing.expectEqual(denominator, value.denominator);
        },
        else => return error.InvalidMetadata,
    }
}

test "generated descriptors carry DSL infinity metadata" {
    try expectFieldInfinity(free_fermion_descriptor, 0, .primary_from_weight, .infer, 0, null, null);
    try expectRationalMetadata(free_fermion_descriptor, 0, 1, 2);
    try expectFieldInfinity(eta_xi_sphere_descriptor, 0, .primary_from_weight, .infer, 0, null, null);
    try expectRationalMetadata(eta_xi_sphere_descriptor, 0, 1, 1);
    try expectFieldInfinity(eta_xi_sphere_descriptor, 1, .primary_from_weight, .infer, 1, null, null);
    try expectRationalMetadata(eta_xi_sphere_descriptor, 1, 0, 1);
    try expectFieldInfinity(eta_xi_torus_descriptor, 0, .primary_from_weight, .infer, 0, null, null);
    try expectRationalMetadata(eta_xi_torus_descriptor, 0, 1, 1);
    try expectFieldInfinity(eta_xi_torus_descriptor, 1, .primary_from_weight, .infer, 1, null, null);
    try expectRationalMetadata(eta_xi_torus_descriptor, 1, 0, 1);
    try expectFieldInfinity(bc_descriptor, 0, .primary_from_weight, .infer, 0, null, null);
    try expectRationalMetadata(bc_descriptor, 0, 2, 1);
    try expectFieldInfinity(bc_descriptor, 1, .primary_from_weight, .infer, 1, null, null);
    try expectRationalMetadata(bc_descriptor, 1, -1, 1);
    try expectFieldInfinity(free_boson_descriptor, 1, .primary_from_weight, .infer, 0, null, null);
    try expectRationalMetadata(free_boson_descriptor, 0, 1, 1);
    try expectFieldInfinity(free_boson_descriptor, 2, .primary_from_weight, .antiholomorphic, null, 0, null);
    try expectRationalMetadata(free_boson_descriptor, 0, 1, 1);
    try expectFieldInfinity(free_boson_descriptor, 3, .branch_global_exponential, .infer, 4, 4, 0);
    try expectFieldInfinity(free_fermion_10_full_descriptor, 0, .primary_from_weight, .infer, 0, null, null);
    try expectRationalMetadata(free_fermion_10_full_descriptor, 0, 1, 2);
    try expectFieldInfinity(free_fermion_10_full_descriptor, 1, .primary_from_weight, .antiholomorphic, 0, null, null);
    try expectRationalMetadata(free_fermion_10_full_descriptor, 0, 1, 2);
    try expectFieldInfinity(eta_xi_sphere_full_descriptor, 0, .primary_from_weight, .infer, 0, null, null);
    try expectRationalMetadata(eta_xi_sphere_full_descriptor, 0, 1, 1);
    try expectFieldInfinity(eta_xi_sphere_full_descriptor, 1, .primary_from_weight, .infer, 1, null, null);
    try expectRationalMetadata(eta_xi_sphere_full_descriptor, 1, 0, 1);
    try expectFieldInfinity(eta_xi_sphere_full_descriptor, 2, .primary_from_weight, .antiholomorphic, 0, null, null);
    try expectRationalMetadata(eta_xi_sphere_full_descriptor, 0, 1, 1);
    try expectFieldInfinity(eta_xi_sphere_full_descriptor, 3, .primary_from_weight, .antiholomorphic, 1, null, null);
    try expectRationalMetadata(eta_xi_sphere_full_descriptor, 1, 0, 1);
    try expectFieldInfinity(eta_xi_torus_full_descriptor, 0, .primary_from_weight, .infer, 0, null, null);
    try expectRationalMetadata(eta_xi_torus_full_descriptor, 0, 1, 1);
    try expectFieldInfinity(eta_xi_torus_full_descriptor, 1, .primary_from_weight, .infer, 1, null, null);
    try expectRationalMetadata(eta_xi_torus_full_descriptor, 1, 0, 1);
    try expectFieldInfinity(eta_xi_torus_full_descriptor, 2, .primary_from_weight, .antiholomorphic, 0, null, null);
    try expectRationalMetadata(eta_xi_torus_full_descriptor, 0, 1, 1);
    try expectFieldInfinity(eta_xi_torus_full_descriptor, 3, .primary_from_weight, .antiholomorphic, 1, null, null);
    try expectRationalMetadata(eta_xi_torus_full_descriptor, 1, 0, 1);
    try expectFieldInfinity(bc_sphere_full_descriptor, 0, .primary_from_weight, .infer, 0, null, null);
    try expectRationalMetadata(bc_sphere_full_descriptor, 0, 2, 1);
    try expectFieldInfinity(bc_sphere_full_descriptor, 1, .primary_from_weight, .infer, 1, null, null);
    try expectRationalMetadata(bc_sphere_full_descriptor, 1, -1, 1);
    try expectFieldInfinity(bc_sphere_full_descriptor, 2, .primary_from_weight, .antiholomorphic, 0, null, null);
    try expectRationalMetadata(bc_sphere_full_descriptor, 0, 2, 1);
    try expectFieldInfinity(bc_sphere_full_descriptor, 3, .primary_from_weight, .antiholomorphic, 1, null, null);
    try expectRationalMetadata(bc_sphere_full_descriptor, 1, -1, 1);
}

/// selfTest validates that generated preset descriptors are loadable.
pub fn selfTest() !void {
    try d.validateDescriptor(free_fermion_descriptor);
    try d.validateDescriptor(eta_xi_sphere_descriptor);
    try d.validateDescriptor(eta_xi_torus_descriptor);
    try d.validateDescriptor(bc_descriptor);
    try d.validateDescriptor(free_boson_descriptor);
    try d.validateDescriptor(free_fermion_10_full_descriptor);
    try d.validateDescriptor(eta_xi_sphere_full_descriptor);
    try d.validateDescriptor(eta_xi_torus_full_descriptor);
    try d.validateDescriptor(bc_sphere_full_descriptor);
}
