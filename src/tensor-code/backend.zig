const decomposition = @import("decomposition.zig");
const projector = @import("projector.zig");
const rendering = @import("rendering.zig");
const root_data = @import("root-data.zig");
const store = @import("representation-store.zig");
const symmetry = @import("symmetry.zig");

/// BackendId names one registered Lie-family backend.
pub const BackendId = u16;

/// PrimitiveInvariantSpan names backend-owned primitive invariant descriptors.
pub const PrimitiveInvariantSpan = struct {
    offset: u32,
    len: u32,
};

/// RenderConvention records the concrete rendering convention passed to a backend.
pub const RenderConvention = struct {
    options: rendering.RenderOptions,
};

/// WeightSystemHandle names one backend-cached weight system.
pub const WeightSystemHandle = struct {
    value: u32,

    /// init constructs a weight-system handle.
    pub fn init(value: u32) WeightSystemHandle {
        return .{ .value = value };
    }
};

/// WeightSystemAudit stores mandatory compact weight-generation counters.
pub const WeightSystemAudit = struct {
    weight_count: u32 = 0,
    total_multiplicity: u128 = 0,
};

/// Capabilities is the internal contract every Lie-family backend must satisfy.
pub const Capabilities = struct {
    validate_algebra: *const fn (*anyopaque, symmetry.SimpleLieAlgebra) anyerror!void,
    irrep_metadata: *const fn (*anyopaque, store.AlgebraHandle, store.IrrepHandle) anyerror!store.IrrepMetadata,
    weight_system: *const fn (*anyopaque, *store.Store, store.AlgebraHandle, store.IrrepHandle) anyerror!WeightSystemHandle,
    decompose_product: *const fn (*anyopaque, *store.Store, *decomposition.Store, decomposition.ProductKey) anyerror!decomposition.ProductDecompositionHandle,
    local_projector: *const fn (*anyopaque, projector.ProjectorKey) anyerror!projector.ProjectorId,
    primitive_invariants: *const fn (*anyopaque, []const store.IrrepHandle) anyerror!PrimitiveInvariantSpan,
    render_projector: *const fn (*anyopaque, projector.ProjectorId, RenderConvention, *anyopaque) anyerror!void,
};

/// Record stores one backend state pointer and capability table.
pub const Record = struct {
    id: BackendId,
    state: *anyopaque,
    family: symmetry.LieFamily,
    root_conventions: root_data.AlgebraConventions,
    capabilities: Capabilities,
};
