/// Symmetry labels a named symmetry algebra.
const Symmetry = struct {
    name: []const u8,
    algebra: LieAlgebra,
};

/// LieAlgebra distinguishes U(1) from simple Lie algebras.
const LieAlgebra = union(enum) {
    u1,
    simple: SimpleLieAlgebra,
};

/// SimpleLieAlgebra stores the simple family and rank.
pub const SimpleLieAlgebra = struct {
    family: LieFamily,
    rank: u8,
};

/// LieFamily names the supported simple Lie families.
pub const LieFamily = enum {
    a,
    b,
    c,
    d,
    e6,
    e7,
    e8,
    f4,
    g2,
};

/// QuantumNumbers is the tensor-product list of representation ids.
pub const QuantumNumbers = []const RepresentationId;

/// SymmetryId names a symmetry in a symmetry store.
pub const SymmetryId = u8;
/// RepresentationId names a representation in a representation store.
pub const RepresentationId = u8;

/// Representation stores a symmetry id and its label.
const Representation = struct {
    symmetry: SymmetryId,
    label: RepresentationLabel,
};

/// RepresentationLabel stores either a rational charge or Dynkin labels.
const RepresentationLabel = union(enum) {
    u1_charge: U1ChargeRational,
    dynkin: []const i8,
};

/// U1ChargeRational stores a rational U(1) charge.
pub const U1ChargeRational = struct {
    numerator: i8,
    denominator: i8,
};

/// TensorIndex stores a representation id and concrete index label.
const TensorIndex = struct {
    representation: RepresentationId,
    label: u32,
};

/// TensorIndexId names a tensor index in a tensor expression.
pub const TensorIndexId = u32;

/// TensorStructure stores simple built-in tensor structures.
pub const TensorStructure = union(enum) {
    none,
    kronecker_delta: struct {
        left: TensorIndexId,
        right: TensorIndexId,
    },
};
