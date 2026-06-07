const operators = @import("../expressions/operators.zig");
const tensor = @import("tensor-code");

/// Id groups compact handles used by CFT and BCFT presets.
pub const Id = struct {
    const Sector = u16;
    const Strategy = u16;
    const StatisticsRule = u16;
    const SectorPresentation = u16;
    const ConformalStructure = u16;
    const QuantumRule = u16;
    const StrategySupportRule = u16;
    const WickRuleSet = u16;
    const Pairing = u16;
    const InversePairing = u16;
    const PairingData = u16;
    const ZeroModeRuleSet = u16;
    const CorrelatorConfig = u16;
    const LocalOpeConfig = u16;
    const CocycleTable = u16;
    /// FiniteProjection names finite projections used by public basis queries.
    pub const FiniteProjection = u16;
    const Lattice = u16;
    const LatticeVector = u32;
    /// ModeAlgebra names a mode algebra used by public descendant filters.
    pub const ModeAlgebra = u16;
    const ModeActionRule = u16;
    const LabelSchema = u16;
    /// LabelSpan names a compact slice of runtime body labels accepted by body builders.
    pub const LabelSpan = u32;
    const Extra = u32;
    const ConventionSet = u16;
    const WeightRule = u16;
    const CFT = u16;
    const LabelMap = u16;
    const BoundaryCondition = u16;
    const BoundaryStack = u16;
    const BoundarySpinData = u16;
    const ChanPatonMatrixUnit = u32;
    const Grading = u16;
};

/// Spec groups bulk CFT and BCFT preset declarations.
pub const Spec = struct {
    const Sector = struct {
        name: []const u8,
        tactic_preference: []const Id.Strategy,
        statistics_rule: Id.StatisticsRule,
        presentations: []const Id.SectorPresentation,
    };

    /// CFT is the compile-time declaration of a bulk CFT preset.
    pub const CFT = struct {
        sectors: []const Sector,
        bulk_operator_kinds: []const operators.OperatorKind,
        conformal_structure: Id.ConformalStructure,
        conformal_structures: []const ConformalStructure,
        quantum_names: []const Label.QuantumName,
        label_schemas: []const Label.Schema,
        conventions: []const Rule.ConventionSet,
        weight_rules: []const Rule.Weight,
        quantum_rules: []const Rule.Quantum,
        statistics_rules: []const Rule.Statistics,
        strategy_support_rules: []const Rule.StrategySupport,
        wick_rule_sets: []const Rule.WickSet,
        pairing_data: []const Rule.PairingData,
        zero_mode_rule_sets: []const Rule.ZeroModeSet,
        correlator_configs: []const Runtime.CorrelatorConfig,
        local_ope_configs: []const Runtime.LocalOpeConfig,
        cocycle_tables: []const Rule.CocycleTable,
        presentations: []const Presentation.Sector,
        finite_projections: []const Rule.FiniteProjection,
        lattices: []const Presentation.Lattice,
        mode_algebras: []const Mode.Algebra,
        mode_action_rules: []const Mode.ActionRule,
    };

    const ConformalStructure = struct {
        stress_tensor: Runtime.OperatorRef,
        susy: WorldsheetSusy,
        supercurrents: []const Runtime.OperatorRef,
        r_currents: []const Runtime.OperatorRef,
    };

    const WorldsheetSusy = enum {
        none,
        n1_1,
        n2_2,
        n1_chiral,
        n2_chiral,
        custom,
    };

    /// BCFT extends a bulk preset with boundary operator and Wick data.
    pub const BCFT = struct {
        name: []const u8,
        bulk: Id.CFT,
        boundary_conditions: []const Boundary.Condition,
        boundary_stacks: []const Boundary.Stack,
        boundary_stress_tensor: Runtime.OperatorRef,
        boundary_spin: []const Boundary.SpinData,
        boundary_operator_kinds: []const operators.OperatorKindId,
        boundary_changing_kinds: []const Boundary.ChangingKind,
        wick_rule_sets: []const Rule.WickSet,
        pairing_data: []const Rule.PairingData,
        zero_mode_rule_sets: []const Rule.ZeroModeSet,
        correlator_configs: []const Runtime.CorrelatorConfig,
        local_ope_configs: []const Runtime.LocalOpeConfig,
    };
};

/// Boundary groups boundary-condition, stack, and Chan-Paton data.
pub const Boundary = struct {
    const Condition = struct {
        name: []const u8,
        simple_data: Id.Extra,
    };

    const Stack = struct {
        name: []const u8,
        entries: []const StackEntry,
    };

    const StackEntry = struct {
        boundary: Id.BoundaryCondition,
        multiplicity: u32,
    };

    /// ChangingKind identifies a boundary-local kind from one condition to another.
    pub const ChangingKind = struct {
        from: Id.BoundaryCondition,
        to: Id.BoundaryCondition,
        kind: operators.OperatorKindId,
    };

    const SpinData = struct {
        id: Id.BoundarySpinData,
    };

    const ChanPatonLabel = struct {
        endpoints: ChanPatonEndpoints,
        factor: ChanPatonFactor,
    };

    const ChanPatonEndpoints = struct {
        from_stack: Id.BoundaryStack,
        to_stack: Id.BoundaryStack,
        from_entry: u32,
        to_entry: u32,
    };

    const ChanPatonFactor = union(enum) {
        matrix_unit: ChanPatonMatrixUnit,
        tensor_factor: tensor.TensorExprId,
    };

    const ChanPatonMatrixUnit = struct {
        row: u32,
        col: u32,
    };
};

/// Label groups quantum-number and operator-label schema declarations.
pub const Label = struct {
    const QuantumName = struct {
        name: []const u8,
    };

    /// QuantumFilter constrains one named quantum-number value.
    pub const QuantumFilter = struct {
        name: u16,
        value: i64,
    };

    const Schema = struct {
        name: []const u8,
        fields: []const Field,
    };

    const Field = struct {
        name: []const u8,
        kind: FieldKind,
    };

    const FieldKind = enum {
        integer,
        rational,
        lattice_vector,
        tensor_expr,
        opaque_data,
    };
};

const Rule = struct {
    const ConventionSet = struct {
        name: []const u8,
    };

    const Weight = struct {
        name: []const u8,
    };

    const Quantum = struct {
        name: []const u8,
    };

    const Statistics = struct {
        name: []const u8,
    };

    const StrategySupport = struct {
        name: []const u8,
    };

    const WickSet = struct {
        name: []const u8,
        conventions: Id.ConventionSet,
    };

    const ZeroModeSet = struct {
        name: []const u8,
    };

    const CocycleTable = struct {
        name: []const u8,
    };

    const FiniteProjection = struct {
        name: []const u8,
    };

    const PairingData = struct {
        sector: Id.Sector,
        pairing: Id.Pairing,
        inverse_pairing: Id.InversePairing,
    };
};

const Presentation = struct {
    const Sector = struct {
        sectors: []const Id.Sector,
        name: []const u8,
        operator_map: []const Map,
        lattice: ?Id.Lattice,
        weight_rule: ?Id.WeightRule,
        wick_rules: ?Id.WickRuleSet,
    };

    const Map = struct {
        from: operators.OperatorKindId,
        to: operators.OperatorKindId,
        label_map: Id.LabelMap,
    };

    const Lattice = struct {
        name: []const u8,
        rank: u16,
        bilinear_form: Id.Extra,
        cocycles: ?Id.CocycleTable,
    };
};

const Mode = struct {
    const Algebra = struct {
        name: []const u8,
        generators: []const Generator,
        action_rule: Id.ModeActionRule,
    };

    const Generator = struct {
        name: []const u8,
        indices: []const IndexSlot,
        statistics: StatisticsData,
    };

    const ActionRule = struct {
        name: []const u8,
    };

    const IndexSlot = struct {
        representation: tensor.RepresentationId,
    };

    const StatisticsData = struct {
        parity: u1,
    };

    const Descendant = struct {
        algebra: Id.ModeAlgebra,
        generator: u16,
        mode_number: Runtime.Rational,
        target: operators.OperatorBodyId,
        labels: Id.LabelSpan,
    };
};

/// Runtime groups small data passed to generic runtime procedures.
pub const Runtime = struct {
    /// CorrelatorConfig selects the Wick and zero-mode rules for a correlator call.
    pub const CorrelatorConfig = struct {
        wick_rules: Id.WickRuleSet,
        zero_modes: Id.ZeroModeRuleSet,
    };

    /// LocalOpeConfig selects the local correlator model used internally by OPE.
    pub const LocalOpeConfig = struct {
        domain: OperatorDomain,
        support: ChiralSupport,
        correlator_config: Id.CorrelatorConfig,
    };

    /// OperatorDomain identifies whether an operator body is bulk or boundary data.
    pub const OperatorDomain = enum {
        bulk,
        boundary,
        boundary_changing,
    };

    /// ChiralSupport records the chiral support of candidates and OPE targets.
    pub const ChiralSupport = enum {
        holomorphic,
        antiholomorphic,
        mixed,
        boundary,
    };

    const OperatorRef = struct {
        kind: operators.OperatorKindId,
        labels: Id.LabelSpan,
    };

    /// ConformalWeights stores holomorphic and antiholomorphic weights.
    pub const ConformalWeights = struct {
        h: ?Rational,
        hbar: ?Rational,
    };

    /// LevelBound limits descendant level in basis or OPE generation.
    pub const LevelBound = struct {
        max: Rational,
    };

    const Rational = struct {
        numerator: i64,
        denominator: i64,
    };
};
