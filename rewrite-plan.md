# Rewrite Plan

## Core correction (from Wolfram modularity docs)
The current anti-pattern is using ``Begin["Private`"]`` inside packages. That creates or reuses the top-level `` Private` `` context and causes global pollution across modules.

Correct package-private usage is ``Begin["`Private`"]``. The leading backtick makes the context relative to the current package context.

Important package-model note:
- Use ``BeginPackage`` only once for the main ``StringCode` `` package.
- ``BeginPackage["Context`"]``/``EndPackage[]`` is not a hierarchical module system; it creates a normal top-level context and adds it to context search path handling.
- Declaring internal "subpackages" with ``BeginPackage`` still creates top-level contexts, so this is not a true encapsulated submodule boundary.
- For internal subpackages/submodules, use only ``Begin["`Submodule`"]``/``End[]`` blocks inside one package file or package-private scope.
- This is why local forwarding helpers are useful: they keep call sites short without exposing or repeatedly typing long absolute context paths.

Observed behavior check:
- ``BeginPackage["Demo`Pkg`"]`` then ``Begin["Private`"]`` sets the current context to global `` Private` ``.
- ``BeginPackage["Demo`Pkg`"]`` then ``Begin["`Private`"]`` sets the current context to package-local `` Demo`Pkg`Private` ``.

## Problems to solve
- Maintainability: helpers from unrelated modules collide because they share top-level `` Private` ``.
- Readability: symbol ownership is unclear without explicit per-module private subcontexts.
- Performance: OPE and NormalOrdering are bottlenecks, but refactors are risky without clean symbol boundaries.

## Success criteria
- No module enters top-level `` Private` `` from package code.
- Every subsystem has explicit, isolated implementation contexts.
- Every nontrivial symbol has usage text immediately above its definition.
- Baseline performance measurements exist before any Rust extraction.

## 1) Namespace plan: no polluted shared private context

### Context structure per subsystem
For each subsystem (example OPE), use:
1. The only package context declaration should be ``BeginPackage["StringCode`"]`` in the top-level loader.
2. Define shared helpers in ``StringCode`Common` `` using ``Begin`` and load that early.
3. Define modules as subcontexts with ``Begin["StringCode`OPE`"]``, ``Begin["StringCode`Brackets`"]``, etc.
4. Keep implementation internals in private subcontexts such as ``StringCode`OPE`Private`Core` `` and ``StringCode`OPE`Private`Projection` ``.

No code in package files should use ``Begin["Private`"]``.

### Top-level loader + module-alias pattern
```wl
(* File: StringCode/StringCode.m *)
BeginPackage["StringCode`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`OPE`"];
Needs["StringCode`Brackets`"];
EndPackage[];
```

```wl
(* File: StringCode/OPE/OPE.m *)
Begin["StringCode`OPE`"];

OPE::usage = "Computes operator product expansions.";
OPEProjected::usage = "Projects OPE terms to requested weights.";

Begin["`Private`"];
Needs["StringCode`Symbols`"];
Needs["StringCode`NormalOrdering`"];
Needs["StringCode`Wick`"];

Begin["`Core`"];
opeCore::usage = "Main rule dispatcher for OPE computation.";
opeCore[args___] := Null;  (* replace with implementation *)
End[];

Begin["`Projection`"];
projectTerm::usage = "Projection helper for weighted OPE terms.";
projectTerm[term_, _] := term;
End[];

OPE[args___] := `Core`opeCore[args];
OPEProjected[wH_, wA_][term_] := `Projection`projectTerm[term, {wH, wA}];
End[];
End[];
```

### Consumer-module example (import once, call short names)
```wl
(* File: StringCode/Brackets/Brackets.m *)
Begin["StringCode`Brackets`"];
Needs["StringCode`OPE`" -> "ope`"];
BracketFromOPE::usage = "Build bracket terms from projected OPE data.";

Begin["`Private`"];
BracketFromOPE[weightH_, weightA_, localOps__] := 
  ope`OPEProjected[weightH, weightA][localOps];
End[];
End[];
```

### Rules for symbol access
- Inside a module-private block, prefer unqualified names.
- Prefer ``Needs["Long`Context`" -> "short`"]`` when you want concise qualified call sites without touching ``$ContextPath``.
- If qualification is needed, qualify to the nearest intended private context, for example `` `Core`opeCore`` from inside ``StringCode`OPE`Private` ``.
- Cross-submodule reuse should happen through explicit package exports, not by relying on a global `` Private` `` dump.

### Migration sequence
1. Replace every ``Begin["Private`"]`` in package files with ``Begin["`Private`"]``.
2. Keep only one package declaration at top-level ``StringCode``; replace module-level ``BeginPackage`` blocks with ``Begin`` blocks.
3. Add ``StringCode`Common` `` only for truly shared helpers; do not use it for symbol-lookup hacks.
4. Split each large private body into named subcontexts (Core, Rules, Simplify, Projection, etc.) inside module contexts.
5. Replace ad-hoc global wrapper injection with per-module ``Needs["Long`Context`" -> "short`"]`` alias declarations.
6. Keep exported signatures unchanged while moving internals.
7. Add smoke checks after each move: Context[sym] and Length[DownValues[sym]].

## 2) Data model plan (tagged variants, module-local types)

Use head-based variants plus predicates, defined in a dedicated private type submodule.

	(* File: StringCode/OPE/OPE.m, inside Begin["`Private`"] *)
	Begin["`Types`"];
	
	FieldTermQ::usage = "True when expr is a supported field-term variant.";
	FieldTermQ[_BosonTerm | _FermionTerm | _GhostTerm] := True;
	FieldTermQ[_] := False;
	
	BosonTermQ::usage = "True when expr is a BosonTerm with valid shape.";
	BosonTermQ[expr_] := MatchQ[expr, BosonTerm[_Integer, _]];
	MakeBosonTerm::usage = "Construct a BosonTerm with basic validation.";
	MakeBosonTerm[index_Integer, z_] := BosonTerm[index, z];
	
	FermionTermQ::usage = "True when expr is a FermionTerm with valid shape.";
	FermionTermQ[expr_] := MatchQ[expr, FermionTerm[_Integer, _]];
	MakeFermionTerm::usage = "Construct a FermionTerm with basic validation.";
	MakeFermionTerm[index_Integer, z_] := FermionTerm[index, z];
	
	GhostTermQ::usage = "True when expr is a GhostTerm with valid shape.";
	GhostTermQ[expr_] := MatchQ[expr, GhostTerm[_String, _]];
	MakeGhostTerm::usage = "Construct a GhostTerm with basic validation.";
	MakeGhostTerm[species_String, z_] := GhostTerm[species, z];
	
	End[];

## 3) Performance plan (after context cleanup)

### Stage A: baseline first
1. Build deterministic benchmark inputs for NormalOrdering and OPE.
2. Record RepeatedTiming across small/medium/large workloads.
3. Capture ByteCount and LeafCount at key recursive checkpoints.

### Stage B: Mathematica optimization pass
1. Reduce repeated Expand and redundant tree traversals.
2. Reuse normalized intermediate forms in recursive calls.
3. Memoize pure helper computations where inputs are stable.

### Stage C: Rust extraction gate
Move code to Rust only if:
- kernel-side bottlenecks remain after Stage B,
- IO schema is stable,
- crossing overhead is lower than expected compute savings.

Likely first candidates: contraction bookkeeping in NormalOrdering and repeated term partition/classification in OPE.

## 4) Verification and rollout
- Add conformance checks per migrated subsystem:
  - context ownership checks (Context, Names),
  - behavior parity against current outputs,
  - timing guardrails.
- Roll out in order: Wick, NormalOrdering, OPE.
- Keep facade signatures stable during migration.

## 5) Immediate next actions
1. Patch all package files to eliminate ``Begin["Private`"]`` usage.
2. Collapse redundant OPE/OPE.API split into one exported package context unless there is a truly separate contract boundary.
3. Introduce first two OPE private submodules (Core and Projection).
4. Add type submodule (Types) and predicates for first OPE term variants.
5. Capture and store baseline benchmark numbers before Rust work.
