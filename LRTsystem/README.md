# Coefficient systems of App. *app:Cn* and App. *app:Diffeo*: StringCode pipelines

Two Wolfram Language pipelines that build, print and solve the linear systems that fix

- **LRTsystem.wl**: the coefficients of 𝒞ₙ and the mass Mₙ, from the oscillator components of the level-n linearized EOM (App. *app:Cn*), for n = 1, 2 on the d = 5, 4, 3 backgrounds;
- **Diffeosystem.wl**: the field redefinition F_H, from the 𝒱ₙ component of eq. (*diffeoDemand*) (App. *app:Diffeo*), for n = 1, 2.

Everything needed for n = 1 is included; n = 2 additionally needs `data/fullLevel2.mx` for the 𝒞ₙ pipeline (see below). Both follow the same four steps:

1. split the input into its components;
2. print the equations and compare them with the draft;
3. solve them;
4. print the solution and compare it with the draft.

## Requirements

- Mathematica (tested with 15.0) and the StringCode package, installed so that `Needs["StringCode`"]` works.
- For background runs, a macOS or Linux shell; the worker scripts can also be run by hand (see below).

## Layout

| path | content |
|---|---|
| `LRTsystem.wl`, `LRTbrackets.wls` | 𝒞ₙ pipeline and its background worker (one bracket part per kernel) |
| `Diffeosystem.wl`, `Diffeobrackets.wls` | F_H pipeline and the worker computing the bracket [λ₀ ⊗ 𝒱ₙ[T⁽⁰⁾]] |
| `Diffeohalves.wls` | the same bracket for one half of λ₀, with the unpolarized seed (bDiff at n = 1; n2OPE, n2Raised at n = 2) |
| `helpers/` | vertex constructors, draft formulas and source evaluation used by `LRTsystem.wl` |
| `data/Qlambda{1,2}paper.m` | StringCode BRST action of the compensator basis elements (𝒫, 𝒬 and their mirrors) with general profiles λn[k] |
| `data/basis{1,2}Projected.m` | the mass-level-n operator basis from which 𝒞ₙ is drawn |
| `data/fullLevel1.m` | the recorded level-1 EOM: brackets of the background with the LRT vertex, plus Q𝒞₁ and the kinetic term (input of Step 1 of `LRTsystem.wl` at n = 1) |
| `data/fullLevel2.mx` | **not included** (362 MB): the same at level 2. Place it here to run Step 1 of `LRTsystem.wl` at n = 2 |
| `cache/` | created on first use; all intermediate and final results (`.mx`) |

Every path is relative to this folder. To use other locations, set `LRT$Data`, `LRT$Cache`, `LRT$Helpers` (or `DF$Data`, `DF$Cache`) before `Get`.

## Running

In a notebook (or `wolframscript`):

```mathematica
Needs["StringCode`"];
InitStringCode[<|"theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];
```

### 𝒞ₙ and Mₙ

```mathematica
Get["/path/to/this/folder/LRTsystem.wl"]; LRTInit[];
LRTSplit[n];                 (* Step 1: split data/fullLevel_n into Q C_n, kinetic and bracket parts; LRTSplit[n, expr] for an expression in memory *)
LRTRunBrackets[n];           (* bracket parts evaluated on the backgrounds in background kernels *)
LRTBracketStatus[n]          (* wait until every part reports "saved" *)
comps = LRTComponents[n, d]; (* all oscillator components of the EOM, d = 5, 4, 3 *)
LRTPrintSystem[comps]; LRTCompareWithDraft[comps];   (* Step 2 *)
sol = LRTSolve[comps];                               (* Step 3 *)
LRTPrintSolution[comps, sol];                        (* Step 4 *)
```

`fullLevel<n>` may name the seed slots freely (`LRT1[U1, a1, a2, a3, a4, 0, 0]` or `m1, …`; `LRTSplit` reads them from the data), and its brackets may be given raw or after `twoBracketReplRule`. Build its BRST and bracket terms **without `ContractDelta`** (`derAppend[EffectiveBracket[…]]`): applied before every derivative factor is merged into its profile, `ContractDelta` renames indices in a `der[…]` factor and not in the profile, and the EOM comes out wrong. `LRTSplit` stops if it finds contracted seed slots; any puncture placeholder left after the chart stops the run as well.

Unknowns: `acoef[l]`, `bcoef[l]` (l = 1..5), `ccoef[l]` (l = 1..26) as in App. *app:Cn*, at n = 1 also `aT`, `bT`, and `M` = Mₙ. The draft's free parameter δₙ is `del`.

Each bracket part saves, in `cache/`, the expanded and pruned bracket terms (`L<n>X_*.mx`), their contracted background-independent form (`L<n>C_*.mx`) and the background-evaluated source per d (`L<n>S_*_d<d>.mx`).

### F_H

```mathematica
Get["/path/to/this/folder/Diffeosystem.wl"];
DFRunBracket[n]; DFBracketStatus[n]   (* [lambda0 (x) V_n[T0]] with StringCode EffectiveBracket at levels (n, n) *)
comps = DFComponents[n];              (* Step 1: bracket + Q lambda_n - V_n[L_{V/8} T0] - V_n[F_{dV H}(T0)] *)
DFCompareWithDraft[comps]; DFPrintSystem[comps];   (* Step 2 *)
sol = DFSolve[comps];                              (* Step 3 *)
DFPrintSolution[comps, sol];                       (* Step 4 *)
```

`DFComponents[n, "draft"]` uses the draft's bracket formula instead of the StringCode bracket. `DFComponents[n, expr, factor]` takes a bracket computed elsewhere, for example `bDiff` or `n2Raised` from `Diffeohalves.wls` (`Get[DFCacheFile["D1_bDiff.mx"]]`). Such a bracket must use seed profile `U1`/`U2` and gauge profile `V[μ]`, and is multiplied by `factor` (e.g. 2 for one half of λ₀ when both halves contribute equally). Step 2 prints the ratio to the draft's formula on every structure.

Method: every term is linear in V and in T⁽⁰⁾ = e^{ik·X}u^{⊗s}, s = 2n+2. V is a general cubic, so its jets ∂…∂V_a (at most three derivatives) are independent. The 𝒱ₙ component is projected onto its totally symmetric part by contracting the s indices with a generic vector w. Each scalar equation is the coefficient of one V jet times (u·w)^a (k·w)^b (w·w)^c. The unknowns are:

- the coefficients `fH[i]` of the general F_H, which is linear in H with at most two derivatives (k's included);
- the coefficients `lam[l, j]` of general profiles for the four compensator basis elements.

Step 4 prints F_H as the draft's (or a particular) solution plus its free directions. These come in two kinds: combinations that drop out of F_{δ_V H}, i.e. terms linear in the linearized Ricci tensor, and combinations absorbed by Qλₙ.

### Worker scripts by hand

```sh
wolframscript -file LRTbrackets.wls <n> <grav|aux|dil> <part>
wolframscript -file Diffeobrackets.wls <n> cache
wolframscript -file Diffeohalves.wls <1|2> cache
```

## Conventions

- α′ = 1, E = 2√n; N_n and the phase e^{−iEt} are stripped.
- Bracket chart: punctures at ±1/2, so the (2z)^{k·p} kernel is 1; momentum-dependent exponents are dropped; the uniform power of r₀ carried by every bracket term is reported and dropped.
- 𝒞ₙ: H_StringCode = 4h⁽²⁾ and the heat factor e^{(b/2)□}; b must cancel.
- F_H: index labels `p` = u, `kk` = k, `w`, `tr` (traced pair); u·u = u·k = 0, k·k = −4n, so the arithmetic is exact over ℚ(i).
