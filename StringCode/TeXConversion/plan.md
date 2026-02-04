Design a detailed implementation plan for a TeX conversion module in a Mathematica string theory package. Below is everything you need to know.

## Plan

- Implement the general logic of taking some sum of normal-ordered products/operators and converting each symbol in them
- The conversion of theory-specific (or CFT-specific) symbols should be defined in separate submodules

## Example input/output
- Input: R[ProfileX[h[\[Mu],\[Nu]],{\[Lambda]},0,0],c[0,0],ct[0,0],dX[\[Rho],0,0],dXt[\[Sigma],0,0]]
- Output: \\partial_\\lambda h_{\\mu \\nu} c \\bar{c} \\partial X^\rho \\bar{\\partial} X^\\sigma(0)

- Input: R[c[z,1], bt[w,2]]
- Output: \\partial c(z) \\bar{\\partial}^2 \\bar{b}(w)

- Input: R[c[z,1], bt[w,2]] + 2 R[c[z,0], bt[w,0]]
- Output: \\partial c(z) \\bar{\\partial}^2 \\bar{b}(w) + 2 c(z) b(w)

- Input: Op[R[c[0,0], ct[0,0]], Interacting[V[0,0,0,0]]]
- Output: c\\bar{c}V(0)

- Input: R[expX[k1,z,zbar], dX[\[Mu],0,0]]
- Output: e^{i k_1 \\cdot X}(z, \\bar{z}) \\partial X^\\mu
---

## EXISTING CODEBASE PATTERNS

The package lives under `StringCode/`. Every module mirrors this folder hierarchy:

```
StringCode/
├── StringCode.m              # Master init: InitStringCode[<|"theory"→..., "CFT"→...|>]
├── Symbols/
│   ├── Symbols.m             # Base: declares b, c, bt, ct; holomorphicFields, antiHolomorphicFields lists
│   ├── Bosonic/
│   │   ├── Bosonic.m         # Thin stub: just extends ghostNumber rules
│   │   ├── FlatSpace/
│   │   │   └── FlatSpace.m   # Adds dX, dXt, expX, expXHolo, expXAntiHolo, ProfileX + variants
│   │   └── MinimalModel/
│   │       └── MinimalModel.m # Adds V (interacting operator)
│   └── TypeII/
│       ├── TypeII.m          # Adds dΦ, dΦt, ξ, ξt, η, ηt, expΦf, expΦb, expΦtf, expΦtb
│       └── FlatSpace/
│           └── FlatSpace.m   # Adds dX, dXt, expX, ProfileX, ψ, ψt (free boson + fermion)
```

- The TeXConversion file should export a single public function `ToTeX`, all others are in Private context.
- All of the imports are handled correctly, do not worry about that (can use dX instead of Symbols`dX etc.)

---

## FIELD ARGUMENT CONVENTIONS (critical for pattern matching)

From the README and source code:

| Field | Arguments | Meaning |
|-------|-----------|---------|
| `c[n, z]` | derivative count, position | ∂ⁿc(z) — holomorphic c-ghost |
| `b[n, z]` | derivative count, position | ∂ⁿb(z) — holomorphic b-ghost |
| `ct[n, zbar]` | derivative count, position | ∂̄ⁿc̄(z̄) — antiholomorphic |
| `bt[n, zbar]` | derivative count, position | ∂̄ⁿb̄(z̄) — antiholomorphic |
| `dX[μ, n, z]` | index, deriv count, pos | ∂ⁿ⁺¹Xᵘ(z) — **offset by 1** since dX already has one ∂ |
| `dXt[μ, n, zbar]` | index, deriv count, pos | ∂̄ⁿ⁺¹Xᵘ(z̄) — **offset by 1** |
| `ψ[μ, n, z]` | index, deriv count, pos | ∂ⁿψᵘ(z) — TypeII only |
| `ψt[μ, n, zbar]` | index, deriv count, pos | ∂̄ⁿψ̄ᵘ(z̄) — TypeII only |
| `dΦ[n, z]` | deriv count, pos | ∂ⁿ⁺¹φ(z) — **offset by 1** |
| `dΦt[n, zbar]` | deriv count, pos | ∂̄ⁿ⁺¹φ(z̄) — **offset by 1** |
| `ξ[n, z]` | deriv count, pos | ∂ⁿξ(z) |
| `ξt[n, zbar]` | deriv count, pos | ∂̄ⁿξ̄(z̄) |
| `η[n, z]` | deriv count, pos | ∂ⁿη(z) |
| `ηt[n, zbar]` | deriv count, pos | ∂̄ⁿη̄(z̄) |
| `expΦf[exp, z]` | exponent, pos | e^{exp·φ(z)} — fermionic |
| `expΦb[exp, z]` | exponent, pos | e^{exp·φ(z)} — bosonic (same TeX as fermionic) |
| `expΦtf[exp, zbar]` | exponent, pos | e^{exp·φ(z̄)} — antiholomorphic fermionic |
| `expΦtb[exp, zbar]` | exponent, pos | e^{exp·φ(z̄)} — antiholomorphic bosonic |
| `expX[k, z, zbar]` | momentum, z, zbar | e^{ik·X(z,z̄)} — non-chiral |
| `ProfileX[f, ders, z, zbar]` | profile fn, derivs, z, zbar | f(X(z,z̄)) with derivatives |
| `V[nHolo, nAntiHolo, z, zbar]` | holo derivs, antiholo derivs, positions | Minimal model primary |

### Holomorphic vs Antiholomorphic TeX conventions:
- **Derivatives**: ∂ vs ∂̄ (`\\partial` vs `\\bar{\\partial}`)
- **Ghost/superghost/fermion fields** get barred in antiholomorphic: c↔c̄, b↔b̄, ξ↔ξ̄, η↔η̄, ψ↔ψ̄
- **Matter bosons** (X, φ) do NOT get barred — only the position argument changes to z̄. This matches the README: "dXt[μ, n, zbar] — ∂̄ⁿ⁺¹X^μ(z̄)"
- The `t` suffix in Mathematica symbol names = antiholomorphic. (ct, bt, dXt, dΦt, ξt, ηt, ψt, expΦtf, expΦtb)

### Wrappers to handle:
- `R[field1, field2, ...]` — normal-ordered product → rendered as `:field1 field2 ...:`
- `SF[content]` — string field wrapper → transparent (render content)
- `Op[content]` — local operator wrapper → transparent
- `Interacting[content]` — interacting operator wrapper → transparent

### Arithmetic to handle:
- Arithmetic should be handled with the help of Mathematica's `TeXForm`

---

## TASK
- Currently, there is a basic implementation in TeXConversion and its subdirectories that however does not handle arithmetic correctly yet (should be offloaded to Mathematica's `TeXForm`) and does not handle theory-specific symbols like dX correctly (issues with pattern-matching)
- The pattern-matching issue was because the Fallback is loaded before the theory-specific case is loaded and Mathematica thus executes the fallback first.
---

## IMPLEMENTATION STATUS

### Current Test Results (TeXConversion.test.wlnb)
- Tests pass
- Implement new tests that test arithmetic on b-c ghosts

### Bosonic/FlatSpace/FlatSpace.test.wlnb
- Tests fail: It often happens that `TeXForm` returns `\text{}` but we don't want that as we are in TeX math mode [maybe just every time `TeXForm` acts, remove these `\text{}` wrappers and return what is inside.]. On test 6 `e^{i \text{k1} \cdot X}(w, \text{wbar})`, the `k1` should be `k_1`. On test 7, you should get `h_{\mu\nu}` - this one is tricky as `TeXForm` doesn't recognize that these are supposed to be indices!
- The pattern-matching was resolved by putting the fallback case AFTER defining the theory-specific case. Just a peculiarity with how Mathematica files are being read in order.

### TypeII/TypeII.m
- When there is an exponential with arugment -1, do not write `e^{-1 \phi}`, but write `e^{-\phi}`.

---

## NEW APPROACH: Hybrid with Mathematica's ToTeX

### Strategy
Use Mathematica's built-in `TeXForm` for general expressions (arithmetic, Greek letters, etc.), handle only StringCode-specifics with custom code.

### Benefits
1. Mathematica's `TeXForm` already handles: Plus, Times, Power, Rational, Greek letters, Sqrt
2. Fewer recursion issues - no need to reimplement arithmetic
3. Simpler, more maintainable code

### Core Design

```mathematica
ToTeX[expr_] := Module[{processed},
  processed = processStringCode[expr];
  ToTeX[processed]  (* Use Mathematica's TeXForm for final conversion *)
]
```

**StringCode-specific processing**:
```mathematica
(* Wrappers - R adds colons, others are transparent *)
processStringCode[Ra_/;RTest[Ra]] :=
  ":" <> StringJoin[ToTeX /@ List @@ Ra] <> ":"

processStringCode[Opa_/;OpTest[Opa]] :=
  StringJoin[ToTeX /@ List @@ Opa]

processStringCode[SFa_/;SFTest[SFa]] := ToTeX @@ SFa

(* Field symbols - convert to TeX strings directly *)
processStringCode[c[n_, z_]] := texDeriv[n, True] <> "c" <> texPos[z]
processStringCode[dX[idx_, n_, z_]] :=
  texDeriv[n+1, True] <> "X^{" <> ToTeX[idx] <> "}" <> texPos[z]

(* Pass-through for arithmetic - let ToTeX handle *)
processStringCode[x_?NumericQ] := x
processStringCode[x_Symbol] := x
processStringCode[x_] := x  (* fallback *)
```

### Files Structure
```
TeXConversion/
├── TeXConversion.m              # Base: processStringCode for R, Op, SF, ghosts
├── Bosonic/
│   ├── Bosonic.m                # Stub
│   ├── FlatSpace/FlatSpace.m    # processStringCode for dX, dXt, expX, ProfileX
│   └── MinimalModel/MinimalModel.m  # processStringCode for V
└── TypeII/
    ├── TypeII.m                 # processStringCode for dΦ, ξ, η, expΦ*
    └── FlatSpace/FlatSpace.m    # processStringCode for dX, ψ, ψt
```