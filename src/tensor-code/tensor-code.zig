const context = @import("context.zig");
const coupling = @import("coupling.zig");
const kernel = @import("kernel.zig");
const realization = @import("realization.zig");
const rendering = @import("rendering.zig");
const root_data = @import("root-data.zig");
const store = @import("representation-store.zig");
const symmetry = @import("symmetry.zig");

/// SimpleLieAlgebra stores the simple family and rank.
pub const SimpleLieAlgebra = symmetry.SimpleLieAlgebra;
/// LieFamily names the supported simple Lie families.
pub const LieFamily = symmetry.LieFamily;
/// QuantumNumbers is the tensor-product list of representation ids.
pub const QuantumNumbers = symmetry.QuantumNumbers;
/// RepresentationId names a representation in a representation store.
pub const RepresentationId = symmetry.RepresentationId;
/// TensorStructure stores simple built-in tensor structures.
pub const TensorStructure = symmetry.TensorStructure;

/// AlgebraHandle names a registered Lie algebra in a tensor context.
pub const AlgebraHandle = store.AlgebraHandle;
/// IrrepHandle names an abstract irreducible representation.
pub const IrrepHandle = store.IrrepHandle;
/// RealizationHandle names a concrete index realization of an irrep.
pub const RealizationHandle = realization.RealizationHandle;
/// RealizationChannel selects one irrep copy inside a realization product.
pub const RealizationChannel = realization.RealizationChannel;
/// BasisHandle names a generated invariant basis.
pub const BasisHandle = coupling.BasisHandle;
/// InvariantHandle names one invariant inside a basis.
pub const InvariantHandle = coupling.InvariantHandle;
/// Context is an opaque handle to tensor-code stores and caches.
pub const Context = context.Context;
/// ContextOptions configures algebra and rendering defaults.
pub const ContextOptions = context.ContextOptions;
/// AlgebraConventions selects configurable exact-algebra normalizations.
pub const AlgebraConventions = root_data.AlgebraConventions;
/// AlgebraSpec describes a requested algebra before it is interned.
pub const AlgebraSpec = store.AlgebraSpec;
/// IrrepSpec describes a requested representation before it is interned.
pub const IrrepSpec = store.IrrepSpec;
/// ExternalLeg describes a public invariant leg with named free indices.
pub const ExternalLeg = realization.ExternalLeg;
/// RealizationSpec describes a primitive or projected external index model.
pub const RealizationSpec = realization.RealizationSpec;
/// InvariantBasisRequest is the CFT-facing request for invariant tensors.
pub const InvariantBasisRequest = coupling.InvariantBasisRequest;
/// TensorExpansionTerm stores a CFT coefficient attached to one invariant id.
pub const TensorExpansionTerm = coupling.TensorExpansionTerm;
/// RenderOptions controls streamed invariant rendering.
pub const RenderOptions = rendering.RenderOptions;
/// EvalOptions controls component evaluation of one invariant.
pub const EvalOptions = rendering.EvalOptions;
/// SymbolicTerm stores one streamed coefficient times symbolic atoms.
pub const SymbolicTerm = rendering.SymbolicTerm;
/// SymbolicAtom stores one symbolic invariant contraction atom.
pub const SymbolicAtom = rendering.SymbolicAtom;

/// TensorExprId names a tensor expression stored by tensor-code.
pub const TensorExprId = kernel.TensorExprId;
