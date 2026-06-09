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

const free_fermion_symbols = [_][]const u8{ "free-fermion-10", "spin10", "d5", "psi", "mu", "vector" };
const free_fermion_parameters = [_]d.Parameter{};
const free_fermion_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 1, .kind = .ade_irrep, .group_symbol = 2 },
};
const free_fermion_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .symbol = 5 } },
};
const free_fermion_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .sphere, .coordinate_model = .rational },
};
const free_fermion_fields = [_]d.Field{
    .{ .id = 0, .symbol = 3, .insertion = .single, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 4 }}, .statistics = .fermionic },
};
const free_fermion_metadata = [_]d.MetadataExpr{};
const free_fermion_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .residuals = &.{} },
};
const free_fermion_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 0, .terms = &free_fermion_terms_0 },
};
const free_fermion_zero_modes = [_]d.ZeroModeRule{};
pub const free_fermion_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 2434621218,
    .symbols = &free_fermion_symbols,
    .parameters = &free_fermion_parameters,
    .quantum_numbers = &free_fermion_quantum_numbers,
    .field_quantum_numbers = &free_fermion_field_quantum_numbers,
    .surfaces = &free_fermion_surfaces,
    .fields = &free_fermion_fields,
    .metadata = &free_fermion_metadata,
    .wick_rules = &free_fermion_wick,
    .zero_modes = &free_fermion_zero_modes,
};

/// FreeFermion is the lowered generated preset.
pub const FreeFermion = d.GeneratedTheory(free_fermion_descriptor);

const eta_xi_sphere_symbols = [_][]const u8{ "eta-xi", "ghost-number", "eta", "xi" };
const eta_xi_sphere_parameters = [_]d.Parameter{};
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
    .{ .id = 0, .symbol = 2, .insertion = .single, .labels = &.{}, .statistics = .fermionic },
    .{ .id = 1, .symbol = 3, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .zero_mode_consumable = true },
};
const eta_xi_sphere_metadata = [_]d.MetadataExpr{};
const eta_xi_sphere_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{}, .residuals = &.{} },
};
const eta_xi_sphere_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 1, .terms = &eta_xi_sphere_terms_0 },
};
const eta_xi_sphere_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .kind = .constant_fermion, .consumes = &.{1} },
};
pub const eta_xi_sphere_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 3503175150,
    .symbols = &eta_xi_sphere_symbols,
    .parameters = &eta_xi_sphere_parameters,
    .quantum_numbers = &eta_xi_sphere_quantum_numbers,
    .field_quantum_numbers = &eta_xi_sphere_field_quantum_numbers,
    .surfaces = &eta_xi_sphere_surfaces,
    .fields = &eta_xi_sphere_fields,
    .metadata = &eta_xi_sphere_metadata,
    .wick_rules = &eta_xi_sphere_wick,
    .zero_modes = &eta_xi_sphere_zero_modes,
};

/// EtaXiSphere is the lowered generated preset.
pub const EtaXiSphere = d.GeneratedTheory(eta_xi_sphere_descriptor);

const eta_xi_torus_symbols = [_][]const u8{ "eta-xi", "tau", "ghost-number", "eta", "xi", "prime-log-d" };
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
    .{ .id = 0, .symbol = 3, .insertion = .single, .labels = &.{}, .statistics = .fermionic },
    .{ .id = 1, .symbol = 4, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .zero_mode_consumable = true },
};
const eta_xi_torus_metadata = [_]d.MetadataExpr{};
const eta_xi_torus_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .named_kernel = .{ .symbol = 5, .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .derive_left = true } }}, .tensors = &.{}, .residuals = &.{} },
};
const eta_xi_torus_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 1, .terms = &eta_xi_torus_terms_0 },
};
const eta_xi_torus_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .kind = .constant_fermion, .consumes = &.{1} },
};
pub const eta_xi_torus_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 407931773,
    .symbols = &eta_xi_torus_symbols,
    .parameters = &eta_xi_torus_parameters,
    .quantum_numbers = &eta_xi_torus_quantum_numbers,
    .field_quantum_numbers = &eta_xi_torus_field_quantum_numbers,
    .surfaces = &eta_xi_torus_surfaces,
    .fields = &eta_xi_torus_fields,
    .metadata = &eta_xi_torus_metadata,
    .wick_rules = &eta_xi_torus_wick,
    .zero_modes = &eta_xi_torus_zero_modes,
};

/// EtaXiTorus is the lowered generated preset.
pub const EtaXiTorus = d.GeneratedTheory(eta_xi_torus_descriptor);

const bc_symbols = [_][]const u8{ "bc", "ghost-number", "b", "c" };
const bc_parameters = [_]d.Parameter{};
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
    .{ .id = 0, .symbol = 2, .insertion = .single, .labels = &.{}, .statistics = .fermionic },
    .{ .id = 1, .symbol = 3, .insertion = .single, .labels = &.{}, .statistics = .fermionic, .zero_mode_consumable = true },
};
const bc_metadata = [_]d.MetadataExpr{};
const bc_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.one}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -1, .derive_left = true, .derive_right = true } }}, .tensors = &.{}, .residuals = &.{} },
};
const bc_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 0, .right = 1, .terms = &bc_terms_0 },
};
const bc_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .kind = .top_form_fermion, .consumes = &.{1} },
};
pub const bc_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 4050535685,
    .symbols = &bc_symbols,
    .parameters = &bc_parameters,
    .quantum_numbers = &bc_quantum_numbers,
    .field_quantum_numbers = &bc_field_quantum_numbers,
    .surfaces = &bc_surfaces,
    .fields = &bc_fields,
    .metadata = &bc_metadata,
    .wick_rules = &bc_wick,
    .zero_modes = &bc_zero_modes,
};

/// Bc is the lowered generated preset.
pub const Bc = d.GeneratedTheory(bc_descriptor);

const free_boson_symbols = [_][]const u8{ "free-boson-10", "alpha-prime", "spin10", "d5", "X", "mu", "vector", "dX", "dXt", "eta", "expX", "k" };
const free_boson_parameters = [_]d.Parameter{
    .{ .id = 0, .symbol = 1, .role = .scalar_parameter },
};
const free_boson_quantum_numbers = [_]d.QuantumNumber{
    .{ .id = 0, .symbol = 2, .kind = .ade_irrep, .group_symbol = 3 },
};
const free_boson_field_quantum_numbers = [_]d.FieldQuantumNumber{
    .{ .field = 0, .quantum_number = 0, .value = .{ .symbol = 6 } },
    .{ .field = 1, .quantum_number = 0, .value = .{ .symbol = 6 } },
    .{ .field = 2, .quantum_number = 0, .value = .{ .symbol = 6 } },
};
const free_boson_surfaces = [_]d.Surface{
    .{ .id = 0, .kind = .sphere, .coordinate_model = .rational },
};
const free_boson_fields = [_]d.Field{
    .{ .id = 0, .symbol = 4, .insertion = .pair, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 5 }}, .statistics = .bosonic },
    .{ .id = 1, .symbol = 7, .insertion = .single, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 5 }}, .statistics = .bosonic },
    .{ .id = 2, .symbol = 8, .insertion = .single, .labels = &.{.{ .id = 0, .role = .vector_index, .symbol = 5 }}, .statistics = .bosonic },
    .{ .id = 3, .symbol = 10, .insertion = .pair, .labels = &.{.{ .id = 0, .role = .momentum, .symbol = 11 }}, .statistics = .bosonic, .zero_mode_consumable = true, .weight = 5, .anti_weight = 5 },
};
const free_boson_metadata = [_]d.MetadataExpr{
    .{ .rational = .{ .numerator = 1, .denominator = 4 } },
    .{ .parameter = 0 },
    .{ .field_label = .{ .field = 3, .label = 0 } },
    .{ .bilinear = .{ .left = 2, .right = 2, .form_symbol = 9 } },
    .{ .mul = .{ .left = 1, .right = 3 } },
    .{ .mul = .{ .left = 0, .right = 4 } },
};
const free_boson_terms_0 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .neg_parameter_half = 0 }}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -2, .derive_left = true, .derive_right = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .residuals = &.{} },
};
const free_boson_terms_1 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .neg_parameter_half = 0 }}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .position }, .exponent = -2, .derive_left = true, .derive_right = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .residuals = &.{} },
};
const free_boson_terms_2 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .neg_parameter_half = 0 }}, .coordinates = &.{.{ .logarithm = .{ .left = .{ .side = .left, .slot = .holomorphic }, .right = .{ .side = .right, .slot = .holomorphic } } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .residuals = &.{} },
    .{ .scalars = &.{.{ .neg_parameter_half = 0 }}, .coordinates = &.{.{ .logarithm = .{ .left = .{ .side = .left, .slot = .antiholomorphic }, .right = .{ .side = .right, .slot = .antiholomorphic } } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .residuals = &.{} },
};
const free_boson_terms_3 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .neg_parameter_half = 0 }}, .coordinates = &.{.{ .logarithm = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .holomorphic }, .derive_left = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .residuals = &.{} },
};
const free_boson_terms_4 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .neg_parameter_half = 0 }}, .coordinates = &.{.{ .logarithm = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .antiholomorphic }, .derive_left = true } }}, .tensors = &.{.{ .metric = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .residuals = &.{} },
};
const free_boson_terms_5 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .neg_i_parameter_half = 0 }}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .holomorphic }, .exponent = -1, .derive_left = true } }}, .tensors = &.{.{ .momentum_index = .{ .momentum = .{ .side = .right, .slot = 0 }, .index = .{ .side = .left, .slot = 0 } } }}, .residuals = &.{.right} },
};
const free_boson_terms_6 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .neg_i_parameter_half = 0 }}, .coordinates = &.{.{ .difference_power = .{ .left = .{ .side = .left, .slot = .position }, .right = .{ .side = .right, .slot = .antiholomorphic }, .exponent = -1, .derive_left = true } }}, .tensors = &.{.{ .momentum_index = .{ .momentum = .{ .side = .right, .slot = 0 }, .index = .{ .side = .left, .slot = 0 } } }}, .residuals = &.{.right} },
};
const free_boson_terms_7 = [_]d.WickTerm{
    .{ .scalars = &.{.{ .parameter_half = 0 }}, .coordinates = &.{ .{ .green_exponential = .{ .left = .{ .side = .left, .slot = .holomorphic }, .right = .{ .side = .right, .slot = .holomorphic } } }, .{ .green_exponential = .{ .left = .{ .side = .left, .slot = .antiholomorphic }, .right = .{ .side = .right, .slot = .antiholomorphic } } } }, .tensors = &.{.{ .momentum_pair = .{ .left = .{ .side = .left, .slot = 0 }, .right = .{ .side = .right, .slot = 0 } } }}, .residuals = &.{ .left, .right } },
};
const free_boson_wick = [_]d.WickRule{
    .{ .surface = 0, .left = 1, .right = 1, .terms = &free_boson_terms_0 },
    .{ .surface = 0, .left = 2, .right = 2, .terms = &free_boson_terms_1 },
    .{ .surface = 0, .left = 0, .right = 0, .terms = &free_boson_terms_2 },
    .{ .surface = 0, .left = 1, .right = 0, .terms = &free_boson_terms_3 },
    .{ .surface = 0, .left = 2, .right = 0, .terms = &free_boson_terms_4 },
    .{ .surface = 0, .left = 1, .right = 3, .terms = &free_boson_terms_5 },
    .{ .surface = 0, .left = 2, .right = 3, .terms = &free_boson_terms_6 },
    .{ .surface = 0, .left = 3, .right = 3, .terms = &free_boson_terms_7 },
};
const free_boson_zero_modes = [_]d.ZeroModeRule{
    .{ .surface = 0, .kind = .boson_momentum_conservation, .consumes = &.{3}, .two_pi_power = 10 },
};
pub const free_boson_descriptor = d.Descriptor{
    .theory_symbol = 0,
    .theory_hash = 4272003766,
    .symbols = &free_boson_symbols,
    .parameters = &free_boson_parameters,
    .quantum_numbers = &free_boson_quantum_numbers,
    .field_quantum_numbers = &free_boson_field_quantum_numbers,
    .surfaces = &free_boson_surfaces,
    .fields = &free_boson_fields,
    .metadata = &free_boson_metadata,
    .wick_rules = &free_boson_wick,
    .zero_modes = &free_boson_zero_modes,
};

/// FreeBoson is the lowered generated preset.
pub const FreeBoson = d.GeneratedTheory(free_boson_descriptor);

/// selfTest validates that generated preset descriptors are loadable.
pub fn selfTest() !void {
    try d.validateDescriptor(free_fermion_descriptor);
    try d.validateDescriptor(eta_xi_sphere_descriptor);
    try d.validateDescriptor(eta_xi_torus_descriptor);
    try d.validateDescriptor(bc_descriptor);
    try d.validateDescriptor(free_boson_descriptor);
}
