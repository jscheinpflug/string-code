const geometry = @import("local_geometry_reducer.zig");
const scheme = @import("scheme.zig");
const counterterms = @import("counterterms.zig");
const rnc = @import("rnc_vertices.zig");
const plan = @import("diagram_plan.zig");
const wick = @import("wick_signatures.zig");
const reduce = @import("kernel_signature_reducer.zig");
const pole = @import("pole_extractor.zig");
const beta = @import("beta_assembly.zig");

/// GeometryFlavor selects the target-geometry quotient used by local reducers.
pub const GeometryFlavor = geometry.GeometryFlavor;
/// TensorSlotSort classifies a target tensor slot by complex type and variance.
pub const TensorSlotSort = geometry.TensorSlotSort;
/// TensorSlot is one compact target-index occurrence in a local tensor atom.
pub const TensorSlot = geometry.TensorSlot;
/// TensorAtom is one local geometry tensor row.
pub const TensorAtom = geometry.TensorAtom;
/// TensorTerm is a streamed product of local geometry atoms.
pub const TensorTerm = geometry.TensorTerm;
/// ReductionOptions selects the local quotient checks applied to one term.
pub const ReductionOptions = geometry.ReductionOptions;
/// ReductionSummary reports the reducer decision without materializing a sum.
pub const ReductionSummary = geometry.ReductionSummary;
/// reduceLocalTerm filters one streamed local geometry term into caller storage.
pub const reduceLocalTerm = geometry.reduceLocalTerm;
/// WorldsheetModel selects the free-field content used by the RNC job.
pub const WorldsheetModel = rnc.WorldsheetModel;
/// FieldKind identifies one quantum fluctuation field in an RNC vertex.
pub const FieldKind = rnc.FieldKind;
/// BackgroundLegKind identifies one uncontracted local operator leg.
pub const BackgroundLegKind = rnc.BackgroundLegKind;
/// WorldsheetDerivatives records the holomorphic and antiholomorphic derivative count.
pub const WorldsheetDerivatives = rnc.WorldsheetDerivatives;
/// VertexField is one quantum field occurrence inside a local RNC vertex.
pub const VertexField = rnc.VertexField;
/// BackgroundLeg is one local operator leg that survives Wick contraction.
pub const BackgroundLeg = rnc.BackgroundLeg;
/// VertexTensorKind names the target-space tensor atom attached to a vertex.
pub const VertexTensorKind = rnc.VertexTensorKind;
/// VertexTensor is one target-space tensor factor carried by a vertex.
pub const VertexTensor = rnc.VertexTensor;
/// VertexSymmetry stores the explicit combinatorial denominator of one vertex family.
pub const VertexSymmetry = rnc.VertexSymmetry;
/// RncVertexRow is one streamed local RNC interaction or free quadratic row.
pub const RncVertexRow = rnc.RncVertexRow;
/// RncRequest selects the bootstrap vertex families emitted by the first generator.
pub const RncRequest = rnc.RncRequest;
/// streamBootstrapVertices emits the first fixed metric-sector RNC vertex families.
pub const streamBootstrapVertices = rnc.streamBootstrapVertices;
/// BackgroundLegCount fixes the local operator signature required at the end of one branch.
pub const BackgroundLegCount = plan.BackgroundLegCount;
/// DiagramPlanRequest selects the candidate multiset families enumerated from one vertex catalog.
pub const DiagramPlanRequest = plan.DiagramPlanRequest;
/// VertexMultiplicity records one catalog row and its multiplicity in a candidate multiset.
pub const VertexMultiplicity = plan.VertexMultiplicity;
/// DiagramCandidateRow is one compact candidate multiset before explicit Wick pairing.
pub const DiagramCandidateRow = plan.DiagramCandidateRow;
/// streamDiagramCandidates enumerates candidate vertex multisets for one requested loop order.
pub const streamDiagramCandidates = plan.streamDiagramCandidates;
/// WickSignatureRow is one pairable candidate summary before explicit branch generation.
pub const WickSignatureRow = wick.WickSignatureRow;
/// WickSignatureSummary reports how many candidates survive the pairability checks.
pub const WickSignatureSummary = wick.WickSignatureSummary;
/// streamWickSignatures emits the pairable species-count summary of each candidate multiset.
pub const streamWickSignatures = wick.streamWickSignatures;
/// KernelReductionRequest fixes the renormalization metadata attached to emitted kernel rows.
pub const KernelReductionRequest = reduce.KernelReductionRequest;
/// KernelReductionSummary reports how many candidates were lowered successfully.
pub const KernelReductionSummary = reduce.KernelReductionSummary;
/// streamKernelTerms lowers candidate vertex multisets to reduced kernel-signature rows.
pub const streamKernelTerms = reduce.streamKernelTerms;
/// streamKernelTermsFromWickSignatures lowers candidate data with an optional pairability summary.
pub const streamKernelTermsFromWickSignatures = reduce.streamKernelTermsFromWickSignatures;
/// EpsilonSign fixes whether the regulated dimension is 2-epsilon or 2+epsilon.
pub const EpsilonSign = scheme.EpsilonSign;
/// SubtractionScheme selects the pole-subtraction convention.
pub const SubtractionScheme = scheme.SubtractionScheme;
/// BFieldEpsilonScheme records the antisymmetric-tensor epsilon-frame policy.
pub const BFieldEpsilonScheme = scheme.BFieldEpsilonScheme;
/// DimRegMS describes one dimensional-regularization/minimal-subtraction scheme.
pub const DimRegMS = scheme.DimRegMS;
/// stringbookMS returns the fixed dimensional-regularization/minimal-subtraction scheme.
pub const stringbookMS = scheme.stringbookMS;
/// Rational stores one compact exact coefficient.
pub const Rational = counterterms.Rational;
/// LocalCountertermKind names the local operator basis used by renormalization.
pub const LocalCountertermKind = counterterms.LocalCountertermKind;
/// KernelFamily identifies one regulated loop-integral family.
pub const KernelFamily = counterterms.KernelFamily;
/// KernelSignature stores the reduced loop-kernel descriptor emitted by one branch.
pub const KernelSignature = counterterms.KernelSignature;
/// PoleRow is one local pole term emitted after loop-kernel evaluation.
pub const PoleRow = counterterms.PoleRow;
/// BetaRow is one assembled simple-pole contribution in the operator basis.
pub const BetaRow = counterterms.BetaRow;
/// KernelTermRow is one reduced local branch before pole extraction.
pub const KernelTermRow = pole.KernelTermRow;
/// LocalityClass records whether one master family contributes a local pole.
pub const LocalityClass = pole.LocalityClass;
/// PoleResidue stores one Laurent-coefficient contribution for a matched rule.
pub const PoleResidue = pole.PoleResidue;
/// KernelPoleRule maps one reduced kernel signature to local pole data.
pub const KernelPoleRule = pole.KernelPoleRule;
/// PoleExtractionSummary reports how the kernel rows were classified.
pub const PoleExtractionSummary = pole.PoleExtractionSummary;
/// stringbookBootstrapRules returns the first explicit rule table used for low-loop checks.
pub const stringbookBootstrapRules = pole.stringbookBootstrapRules;
/// extractPoleRows matches reduced kernel signatures to explicit local pole rules.
pub const extractPoleRows = pole.extractPoleRows;
/// BetaAssemblyOptions selects the subset of pole rows converted to beta rows.
pub const BetaAssemblyOptions = beta.BetaAssemblyOptions;
/// BetaAssemblySummary reports how the pole stream was consumed.
pub const BetaAssemblySummary = beta.BetaAssemblySummary;
/// assembleBetaRows converts simple-pole rows in the fixed MS scheme to beta rows.
pub const assembleBetaRows = beta.assembleBetaRows;

test "nlsm root exposes only compact local reducer rows" {
    const testing = @import("std").testing;
    try testing.expect(@hasDecl(@This(), "GeometryFlavor"));
    try testing.expect(@hasDecl(@This(), "TensorSlotSort"));
    try testing.expect(@hasDecl(@This(), "reduceLocalTerm"));
    try testing.expect(@hasDecl(@This(), "RncVertexRow"));
    try testing.expect(@hasDecl(@This(), "DiagramCandidateRow"));
    try testing.expect(@hasDecl(@This(), "WickSignatureRow"));
    try testing.expect(@hasDecl(@This(), "streamKernelTerms"));
    try testing.expect(@hasDecl(@This(), "stringbookMS"));
    try testing.expect(@hasDecl(@This(), "PoleRow"));
    try testing.expect(@hasDecl(@This(), "extractPoleRows"));
    try testing.expect(@hasDecl(@This(), "assembleBetaRows"));
}
