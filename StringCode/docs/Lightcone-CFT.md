# Lightcone CFT for TypeII Superstrings

This document describes the Lightcone CFT module added to StringCode for calculations in lightcone gauge, particularly useful for pp-wave backgrounds.

> This module was developed with the assistance of [Claude Code](https://claude.ai/claude-code).

## Overview

The Lightcone CFT provides a **2+8 split** of 10D spacetime:
- **Lightcone directions**: `p` (plus, X⁺) and `m` (minus, X⁻)
- **Transverse directions**: integers `1..8` or symbolic indices (`i`, `j`, `iT`, etc.)

Unlike FlatSpace which uses a single index `μ = 1..10` with Kronecker delta `δ[μ,ν]`, Lightcone uses the lightcone metric `η` with:

| Indices | η value |
|---------|---------|
| ηLC[p, m] = ηLC[m, p] | -1 |
| ηLC[p, p] = ηLC[m, m] | 0 |
| ηLC[p, i] = ηLC[m, i] | 0 |
| ηLC[i, j] (transverse) | δT[i, j] |

## Initialization

```mathematica
Needs["StringCode`"];

InitStringCode[<|
  "theory" -> "TypeII",
  "CFT" -> "Lightcone",
  "conventions" -> "TypeII-Lightcone",
  "bracket" -> "Flat"
|>];
```

## Symbolic Index Convention

All transverse indices are treated **symbolically** (similar to how FlatSpace treats `μ`, `ν`):

```mathematica
(* Any symbol that is not p or m is a transverse index *)
transverseIndexQ[i]   (* True for i, j, k, iT, etc. *)
transverseIndexQ[3]   (* True for integers 1..8 *)
transverseIndexQ[p]   (* False *)
transverseIndexQ[m]   (* False *)
```

This allows writing compact expressions with implicit Einstein summation:

```mathematica
(* Vacuum state with symbolic transverse indices *)
R[expX[pM, z, zbar], c[0,z], ct[0,zbar], 
  expΦf[-1,z], ψ[i,0,z], expΦtf[-1,zbar], ψt[j,0,zbar]]
```

## Matter Fields

| Field | Description | Example |
|-------|-------------|---------|
| `dX[idx, n, z]` | Holomorphic ∂ⁿ⁺¹X | `dX[p, 0, z]` = ∂X⁺ |
| `dXt[idx, n, zbar]` | Antiholomorphic ∂̄ⁿ⁺¹X | `dXt[m, 0, zbar]` = ∂̄X⁻ |
| `ψ[idx, n, z]` | Holomorphic matter fermion | `ψ[i, 0, z]` = ψⁱ |
| `ψt[idx, n, zbar]` | Antiholomorphic matter fermion | `ψt[3, 0, zbar]` = ψ̃³ |

Where `idx` can be:
- `p` or `m` for lightcone directions
- An integer `1..8` for specific transverse directions
- A symbol (`i`, `j`, `iT`, etc.) for symbolic transverse indices

## Wick Contractions

Contractions produce metric factors that stay symbolic until explicitly contracted:

```mathematica
(* Lightcone contractions give η factors *)
Wick[ψ[p, 0, z], ψ[m, 0, w]]  (* → ηLC[p,m]/(z-w) *)
Wick[ψ[p, 0, z], ψ[p, 0, w]]  (* → 0, since ηLC[p,p] = 0 *)

(* Transverse contractions give δT factors *)
Wick[ψ[i, 0, z], ψ[j, 0, w]]  (* → δT[i,j]/(z-w) *)

(* To evaluate metric components *)
ContractLightcone[expr]  (* ηLC[p,m] → -1, etc. *)
ContractDeltaT[expr]     (* δT[i,i] → 8 for traces *)
```

## Conventions (Tmatter, Gmatter, BRST, PCO)

The `TypeII-Lightcone` conventions define matter currents using the dummy index `iT` for implicit transverse summation:

```mathematica
(* T_matter with symbolic transverse sum *)
(* Bosonic: factor of 2 since ∂X commute *)
(* Fermionic: 3 separate terms since ψ don't commute *)
Tmatter[z] =
  -1/αp (2 ηLC[p,m] R[dX[p,0,z], dX[m,0,z]] + R[dX[iT,0,z], dX[iT,0,z]]) +
  (ηLC[p,m] R[ψ[p,0,z], ψ[m,1,z]] + 
   ηLC[m,p] R[ψ[m,0,z], ψ[p,1,z]] + 
   R[ψ[iT,0,z], ψ[iT,1,z]])

(* G_matter with symbolic transverse sum *)
Gmatter[z] =
  -1/√αp (ηLC[p,m] R[ψ[p,0,z], dX[m,0,z]] + 
          ηLC[m,p] R[ψ[m,0,z], dX[p,0,z]] + 
          R[ψ[iT,0,z], dX[iT,0,z]])
```

Available operators:
- `Tmatter[z]`, `Tmatterbar[z]` — Matter stress tensor
- `Gmatter[z]`, `Gmatterbar[z]` — Matter supercurrent
- `Tghost[z]`, `Tghostbar[z]` — Ghost stress tensor
- `Gghost[z]`, `Gghostbar[z]` — Ghost supercurrent
- `Ttotal[z]`, `Gtotal[z]` — Total currents
- `jBRST[z]`, `jBRSTbar[z]` — BRST current
- `PCO[z]`, `PCObar[z]` — Picture changing operators

## TeX Conversion

Lightcone indices render as `+` and `-`:

```mathematica
ToTeX[R[ψ[p, 0, z], ψ[m, 0, w]]]
(* → "\\psi^{+}(z) \\psi^{-}(w)" *)

ToTeX[R[dX[i, 0, z]]]
(* → "\\partial X^{i}(z)" *)
```

## Example: pp-wave Vacuum State

```mathematica
(* From Integrability_SFT.tex equation Grav0 *)
vacuum0[z_, zbar_] := 
  αmm R[expX[pM, z, zbar], c[0,z], ct[0,zbar], 
        expΦf[-1,z], ψ[m,0,z], expΦtf[-1,zbar], ψt[m,0,zbar]] + 
  αij R[expX[pM, z, zbar], c[0,z], ct[0,zbar], 
        expΦf[-1,z], ψ[i,0,z], expΦtf[-1,zbar], ψt[j,0,zbar]] + 
  αmi R[expX[pM, z, zbar], c[0,z], ct[0,zbar], 
        expΦf[-1,z], ψ[m,0,z], expΦtf[-1,zbar], ψt[i,0,zbar]] + 
  αmi R[expX[pM, z, zbar], c[0,z], ct[0,zbar], 
        expΦf[-1,z], ψ[i,0,z], expΦtf[-1,zbar], ψt[m,0,zbar]];

(* Compute OPE *)
OPEProjected[0, 0][ppH0[z, zbar], vacuum0[w, wbar]]

(* Compute bracket *)
BracketProjected[ppH0[z, zbar], ppSol2[w, wbar], 0, 0]
```

## Module Structure

```
StringCode/
├── Symbols/TypeII/Lightcone/Lightcone.m      # Index predicates, η, δT
├── Wick/TypeII/Lightcone/Lightcone.m         # Propagators with lightcone metric
├── OPE/TypeII/Lightcone/Lightcone.m          # OPE extensions
├── Conventions/TypeII/Lightcone/Lightcone.m  # Tmatter, Gmatter, BRST, PCO
├── Brackets/TypeII/Lightcone/Lightcone.m     # Bracket integration
├── Taylor/TypeII/Lightcone/Lightcone.m       # Taylor expansion
├── Operators/TypeII/Lightcone/Lightcone.m    # Operator utilities
├── Correlators/TypeII/Lightcone/Lightcone.m  # Correlator rules
├── BasisGeneration/TypeII/Lightcone/Lightcone.m  # Basis states
└── TeXConversion/TypeII/Lightcone/Lightcone.m    # TeX output
```

---

## TODO: Future Enhancements

### 1. Bosonization Support

Extend the `Bosonize` function to handle lightcone indices:

- [ ] Define mapping of lightcone directions (p, m) to 5-boson charge basis
- [ ] Implement `Bosonize[ψ[p, n, z]]` and `Bosonize[ψ[m, n, z]]`
- [ ] Handle symbolic transverse indices in bosonization
- [ ] Verify cocycle factors for lightcone basis

### 2. Full R-Sector (Spin Fields)

Add spin field support with lightcone spinor decomposition:

- [ ] Define lightcone spinor representations (SO(8) transverse)
- [ ] Implement `S[{spinVec, chirality}, q, modes, n, z]` for lightcone
- [ ] Add spin field OPEs with matter fermions ψ[p], ψ[m], ψ[i]
- [ ] Gamma matrix algebra for SO(1,1) × SO(8) decomposition
- [ ] Picture-raised spin field constructions

### 3. Lightcone Gamma Matrices

- [ ] Implement `GammaUD[p]`, `GammaUD[m]` in lightcone basis
- [ ] SO(8) triality and gamma matrix identities
- [ ] Symbolic gamma contractions with transverse indices

### 4. Testing & Validation

- [ ] Verify `{Q_BRST, Q_BRST} = 0` with lightcone conventions
- [ ] Check `[T, G]` and `[G, G]` OPEs reproduce correct algebra
- [ ] Validate against known pp-wave amplitudes
