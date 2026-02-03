# StringCode

A Mathematica package for algebraic worldsheet calculations in string theory. This library provides tools for computing operator product expansions (OPEs), Wick contractions, normal-ordered products, and string field theory brackets in both bosonic and Type II string theories.

## Overview

StringCode implements the core algebraic structures needed for worldsheet conformal field theory (CFT) calculations in string theory:

- **Normal Ordering**: Grassmann-graded normal-ordered products with automatic sign tracking
- **Wick Contractions**: Propagators for ghost systems (b-c, β-γ) and matter fields
- **Operator Product Expansions**: Recursive OPE computation via Wick's theorem
- **Closed String Field Theory**: BRST cohomology, string brackets, and amplitude calculations
- **Multiple Theories**: Support for bosonic string and Type IIB superstring
- **CFT Backgrounds**: Flat space and minimal model backgrounds

## Installation

Clone the repository and add the package to your Mathematica path:

```mathematica
AppendTo[$Path, "/path/to/string-code"];
Needs["StringCode`"];
```

## Quick Start

Initialize the package with your choice of string theory and conventions:

```mathematica
Needs["StringCode`"];

(* Bosonic string in flat space *)
InitStringCode[<|
  "theory" -> "Bosonic",
  "CFT" -> "FlatSpace",
  "conventions" -> "Bosonic-Xi",
  "bracket" -> "Flat"
|>];

(* Or Type IIB superstring *)
InitStringCode[<|
  "theory" -> "TypeII",
  "CFT" -> "FlatSpace",
  "conventions" -> "TypeII-Xi",  (* or "TypeII-Ashoke" *)
  "bracket" -> "Flat"
|>];
```

## Core Concepts

### Normal-Ordered Products

The `R[...]` function represents a normal-ordered product of worldsheet fields. Fields are automatically sorted with appropriate Grassmann signs:

```mathematica
(* Normal-ordered product of c-ghost and b-ghost *)
R[c[0, z], b[0, w]]

(* Products automatically anticommute for fermions *)
R[b[0, z], c[0, w]] == -R[c[0, w], b[0, z]]

(* Fermionic fields square to zero *)
R[c[0, z], c[0, z]] == 0
```

### Wick Contractions

Wick contractions compute propagators between fields:

```mathematica
(* b-c ghost contraction *)
Wick[R[b[0, z]], R[c[0, w]]]

(* For composite operators *)
DWick[R[a], R[b, c, d]]  (* Contracts a with each element *)
```

### Operator Product Expansions

The `OPE` function computes the full operator product expansion:

```mathematica
(* OPE of two operators *)
OPE[R[c[0, z]], R[b[0, w]]]

(* Nested OPE *)
OPE[R[a], R[b], R[c]]  (* Computes OPE[R[a], OPE[R[b], R[c]]] *)
```

### String Fields and Brackets

String fields are represented using `SF[...]` and placed at positions via local coordinate maps:

```mathematica
(* Define string fields *)
SF1 = SF[R[c[1, z], c[0, z], ct[1, zbar], ct[0, zbar]]];

(* Compute string bracket *)
Bracket[SF1, SF2]

(* Project bracket to specific conformal weights *)
BracketProjected[SF1, SF2, weightHolo, weightAntiHolo]

(* BRST action (1-bracket) *)
actBRST[SF1]
```

## Package Structure

```
StringCode/
├── StringCode.m           # Main entry point, initialization
├── Symbols/               # Field definitions and properties
│   ├── Symbols.m          # Base field classification
│   ├── Bosonic/           # Bosonic string fields (c, b, X, ...)
│   └── TypeII/            # Type II fields (c, b, β, γ, ψ, ...)
├── NormalOrdering/        # Normal-ordered products
│   └── NormalOrdering.m   # R[...] implementation
├── Wick/                  # Wick contractions
│   ├── Wick.m             # Base contraction logic
│   ├── Bosonic/           # Bosonic propagators
│   └── TypeII/            # Type II propagators
├── OPE/                   # Operator product expansions
│   └── OPE.m              # OPE via Wick + normal ordering
├── StringFields/          # String field representations
│   └── StringFields.m     # SF[...] and positioning
├── Operators/             # Multi-local operators
│   └── Operators.m        # MultiOp[...], Op[...]
├── Brackets/              # String field theory brackets
│   └── Brackets.m         # Bracket[...], actBRST[...]
├── Taylor/                # Taylor expansions
│   └── Taylor.m           # TaylorAtOrder[...]
├── Correlators/           # Worldsheet correlators
│   └── Correlators.m      # Corr[...], Vev[...]
├── Conventions/           # Conventions
│   ├── Bosonic/Xi/        # Bosonic conventions
│   └── TypeII/            # Type II conventions
└── BasisGeneration/       # State basis generation
    └── BasisGeneration.m  # generateBasis[...]
```

## Key Functions Reference

| Function | Description |
|----------|-------------|
| `InitStringCode[opts]` | Initialize with theory, CFT, conventions, bracket type |
| `R[...]` | Normal-ordered product of fields |
| `Wick[Ra, Rb]` | Wick contraction between simple fields |
| `DWick[Ra, Rb]` | Wick contraction of simple with composite |
| `OPE[Ra, Rb]` | Full operator product expansion |
| `SF[...]` | String field representation |
| `SFAtPos[SF, z, zbar]` | Place string field at position |
| `Bracket[SF1, SF2, ...]` | Compute n-point string bracket |
| `BracketProjected[..., h, hbar]` | Bracket projected to weight (h, h̄) |
| `actBRST[SF]` | BRST charge action (Q·Ψ) |
| `MultiOp[Op1, Op2, ...]` | Multi-local operator product |
| `TaylorAtOrder[expr, n, z0]` | Taylor expand to order n around z0 |

## Field Notation

Fields are represented as `field[n, position]` where `n` is the number of derivatives, or `field[index, n, position]` for fields with spacetime indices.

### Ghost Sector (universal)

| Field | Description | Ghost # | Weight |
|-------|-------------|---------|--------|
| `c[n, z]` | ∂ⁿc(z) — holomorphic c-ghost | +1 | −1+n |
| `b[n, z]` | ∂ⁿb(z) — holomorphic b-ghost | −1 | +2+n |
| `ct[n, zbar]` | ∂̄ⁿc̄(z̄) — antiholomorphic c-ghost | +1 | −1+n |
| `bt[n, zbar]` | ∂̄ⁿb̄(z̄) — antiholomorphic b-ghost | −1 | +2+n |

For Type II, additional ghost fields include superghosts (β, γ, ξ, η).

### Matter Sector (CFT-dependent)

The matter content depends on the chosen CFT background:

**FlatSpace**: Free bosons and (for Type II) fermions

Chiral fields:
- `dX[μ, n, z]` — ∂ⁿ⁺¹X^μ(z), holomorphic
- `dXt[μ, n, zbar]` — ∂̄ⁿ⁺¹X^μ(z̄), antiholomorphic
- `ψ[μ, n, z]` — worldsheet fermions (Type II only)

Non-chiral fields (depend on both z and z̄):
- `expX[k, z, zbar]` — e^{ik·X}, plane wave vertex operator
- `ProfileX[f, z, zbar]` — f(X), general profile operator

**MinimalModel**: Interacting CFT with Virasoro primaries
- `V[...]` — primary operators of the minimal model

For interacting CFTs, operators are wrapped in `Interacting[...]` to indicate their OPEs are not computed via Wick contractions but are instead specified externally (e.g., from the fusion rules of the minimal model).

## Example: Computing a String Bracket

```mathematica
(* Initialize bosonic string *)
Needs["StringCode`"];
InitStringCode[<|
  "theory" -> "Bosonic",
  "CFT" -> "FlatSpace",
  "conventions" -> "Bosonic-Xi",
  "bracket" -> "Flat"
|>];

(* Define two closed string fields (tachyon vertex operators) *)
V1 = SF[R[c[1, z], ct[1, zbar], expX[k1, z, zbar]]];
V2 = SF[R[c[1, z], ct[1, zbar], expX[k2, z, zbar]]];

(* Compute the 2-bracket *)
result = Bracket[V1, V2];

(* Project to specific weight *)
projected = BracketProjected[V1, V2, 0, 0];
```

## Supported Configurations

| Theory | CFT | Conventions |
|--------|-----|-------------|
| Bosonic | FlatSpace | Bosonic-Xi |
| Bosonic | MinimalModel | Bosonic-Xi |
| TypeII | FlatSpace | TypeII-Xi, TypeII-Ashoke |

## Tests

Test notebooks are located in `Tests/`:

### Unit tests

- `Tests/Unit/Bosonic/OPE-Baisc-Test.wlnb` - Checks of basic OPEs

### Integration tests

- `Tests/Integration/Bosonic/Diffeo-Test.wlnb` - Diffeomorphism invariance checks
- `Tests/Integration/IIB/Ashoke-Test.wlnb` - Type IIB with Ashoke conventions
- `Tests/Integration/IIB/Xi-Test.wlnb` - Type IIB with Xi conventions

## Acknowledgements
This summary was generated by Claude.
