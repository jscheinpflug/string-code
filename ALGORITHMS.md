# StringCode: Algorithm Details

This document describes the internal algorithms and data structures currently used in StringCode. It keeps the original outline, but the implementation details below are updated to match the present codebase.

## Table of Contents

1. [Field Classification](#field-classification)
2. [Normal Ordering](#normal-ordering)
3. [Wick Contractions](#wick-contractions)
4. [Operator Product Expansions](#operator-product-expansions)
5. [Taylor Expansion](#taylor-expansion)
6. [String Bracket Computation](#string-bracket-computation)

---

## Field Classification

### Metadata-Driven Field Registry

Fields are not classified by a single hardcoded table anymore. Instead, `Symbols` registers each field head with

```
DefineField[head, property -> value, ...]
```

The registry stores metadata such as

- statistics (`Boson` or `Fermion`)
- whether the field is `Simple` or `Composite`
- whether it is holomorphic, antiholomorphic, indexed, collapsable, or factorizable
- whether it contributes to regular Grassmann parity
- pairing partners via `PairsWith`
- theory-specific data such as ghost number, conformal weight, factorization rules, picture, and GSO parity

Predicates like `isField`, `isSimple`, `isComposite`, `isCollapsable`, `isFactorizable`, `isHolomorphic`, and `isAntiHolomorphic` are thin wrappers over this metadata.

### Simple vs Composite Fields

- **Simple fields** contract through `Wick` to c-number kernels.
  - Universal examples: `b`, `c`, `bt`, `ct`
  - Flat-space matter derivatives: `dX`, `dXt`
  - Type II additions: `ψ`, `ψt`, `η`, `ηt`, `ξ`, `ξt`, `β`, `βt`, `γ`, `γt`, `dϕ`, `dϕt`, `S`, `St`

- **Composite fields** stay inside operator products and modify the result through `SWick` or `MWick`.
  - Flat-space primaries: `expX`, `expXHolo`, `expXAntiHolo`, `ProfileX`, `ProfileXHolo`, `ProfileXAntiHolo`
  - Type II bosonized exponentials: `expϕb`, `expϕf`, `expϕtb`, `expϕtf`

The `Collapsable` and `Factorizable` tags are separate from the simple/composite split:

- `Collapsable` marks the sector that plain OPE code is allowed to collapse directly.
- `Factorizable` marks mixed-chirality fields that can be split into explicit holomorphic and antiholomorphic pieces during projected OPEs and brackets.

### Pairing Rules

`pairing[{a,b}]` looks up `fieldProperty[a, "PairsWith"]` and `fieldProperty[b, "PairsWith"]`, and returns 1 iff either list contains the other head.

Universal pairings:

```
b ↔ c
bt ↔ ct
```

Bosonic / flat-space examples:

```
dX ↔ dX, expX, ProfileX, expXHolo, ProfileXHolo
dXt ↔ dXt, expX, ProfileX, expXAntiHolo, ProfileXAntiHolo
expX ↔ expX, ProfileX, dX, dXt
ProfileX ↔ ProfileX, expX, dX, dXt
```

Type II examples:

```
ψ ↔ ψ
ψt ↔ ψt
η ↔ ξ
ηt ↔ ξt
β ↔ γ
βt ↔ γt
dϕ ↔ dϕ, expϕb, expϕf
dϕt ↔ dϕt, expϕtb, expϕtf
expϕ* ↔ expϕ* and dϕ / dϕt within the same chirality
```

Because the pairing data lives in the field registry, the contraction logic and the field catalog stay synchronized automatically.

---

## Normal Ordering

The `R[...]` head represents a normal-ordered product of local fields. The implementation does more than simple sorting: it tracks graded commutation signs, strips scalar factors, flattens nested products, and in Type II merges bosonized exponentials at coincident points.

### Sorting and Signs

Out-of-order adjacent entries are reordered by

```
R[..., b, a, ...] -> regcomm[a, b] Canonicalize[R[..., a, b, ...]]
```

when `OrderedQ[{b, a}]` fails.

`regcomm` is theory-specific:

Bosonic theories:

```
regcomm[f, g] = (-1)^(parity[f] parity[g])
```

Type II theories:

```
regcomm[f, g] =
  (-1)^(parity[f] parity[g])
  (-1)^(expϕparity[f] expϕparity[g])
  (-1)^(expϕtparity[f] expϕtparity[g])
```

The extra factors account for the fermionic bosonized exponentials `expϕf` and `expϕtf`.

### Canonicalization

`Canonicalize` sorts the full field list and computes the overall sign in two stages:

1. `SepGradedFields` scans the graded fields and counts how many odd objects have to move past one another.
2. The code multiplies the move count by the signature of the odd fields, then sorts the full list.

Schematically,

```python
def Canonicalize(prod):
    graded = graded_fields(prod)
    moves, oddfields = SepGradedFields(graded)
    sign = (-1)^moves * Signature(oddfields)
    sorted_fields = Sort(list(prod))
    return sign * rebuild(sorted_fields)
```

In Type II, canonicalization also applies `bosExpRules`, which combine bosonized exponentials at the same point after sorting.

### Nilpotency and Exponential Merges

Identical regular fermions still square to zero:

```
R[..., a, a, ...] -> 0    if regparity[a] = 1
```

Type II adds same-point merge rules for bosonized exponentials. Typical examples are:

```
R[..., expϕf[q, z], expϕf[q', z], ...] -> R[..., expϕb[q + q', z], ...]
R[..., expϕb[q, z], expϕf[q', z], ...] -> R[..., expϕf[q + q', z], ...]
```

and similarly in the antiholomorphic sector.

### Linearity, Scalars, and Powers

`R` is multilinear and strips scalar factors:

```
R[..., a + b, ...] -> R[..., a, ...] + R[..., b, ...]
R[..., λ f, ...]   -> λ R[..., f, ...]    if λ contains no fields
R[..., λ, ...]     -> λ R[..., ...]       if λ contains no fields
R[..., R[a, b], ...] -> R[..., a, b, ...]
R[] -> 1
```

Bosonic powers are expanded into repeated factors:

```
R[..., x^n, ...] -> R[..., x, x, ..., x, ...]    if x is bosonic
```

The same normal-ordering layer also provides total ghost number and conformal weight utilities, and Type II extends it with picture and GSO-parity bookkeeping.

---

## Wick Contractions

The Wick layer is split into three basic kernels:

- `Wick` for simple-simple contractions
- `SWick` for simple-composite contractions
- `MWick` for composite-composite contractions

The rules themselves live in theory-specific submodules, while `DWick` and `pairing` provide the shared recursion.

### Fundamental Contractions (`Wick`)

Universal ghost contractions are

```
Wick[b[n, z], c[m, w]]  = (-1)^m ∂_z^(n+m) [1/(z-w)]
Wick[c[m, w], b[n, z]]  = -(-1)^m ∂_z^(n+m) [1/(z-w)]
Wick[bt[n, z], ct[m, w]] = (-1)^m ∂_z^(n+m) [1/(z-w)]
Wick[ct[m, w], bt[n, z]] = -(-1)^m ∂_z^(n+m) [1/(z-w)]
```

Flat-space bosons add

```
Wick[dX[μ, n, z], dX[ν, m, w]]
  = δ^μν (-1)^m ∂_z^(n+m) [(-α'/2)/(z-w)^2]
```

Type II adds, for example,

```
Wick[ψ[μ, n, z], ψ[ν, m, w]]
  = δ^μν (-1)^m ∂_z^(n+m) [fermionToBosonWickRatio/(z-w)]

Wick[η[n, z], ξ[m, w]]
  = (-1)^m ∂_z^(n+m) [1/(z-w)]

Wick[β[n, z], γ[m, w]]
  = -(-1)^m ∂_z^(n+m) [1/(z-w)]

Wick[dϕ[n, z], dϕ[m, w]]
  = (-1)^m ∂_z^(n+m) [-1/(z-w)^2]
```

These kernels are memoized field-by-field to avoid recomputing the same derivatives.

### Simple-Composite Contractions (`SWick`)

`SWick` returns the c-number factor produced when a simple field hits a composite field.

Flat-space examples:

```
SWick[dX[μ, n, z], expX[k, w, w̄]]
  = (-α'/2) (i k^μ) ∂_z^n [1/(z-w)]

SWick[dX[μ, n, z], ProfileX[f, ders, w, w̄]]
  = (-α'/2) der[f][μ] ∂_z^n [1/(z-w)]
```

Type II superghost examples:

```
SWick[dϕ[n, z], expϕb[a, w]]
  = (-a) ∂_z^n [1/(z-w)]

SWick[dϕ[n, z], expϕf[a, w]]
  = (-a) ∂_z^n [1/(z-w)]
```

### Composite-Composite Contractions (`MWick`)

`MWick` returns the multiplicative factor produced by two composite fields.

Flat-space examples:

```
MWick[expX[p, z, z̄], expX[k, w, w̄]]
  = ((z-w)(z̄-w̄))^(α'/2 dot[p, k])

MWick[expX[p, z, z̄], ProfileX[f, ders, w, w̄]]
  = ((z-w)(z̄-w̄))^(-i α'/2 dot[p, der[f]])

MWick[ProfileX[f, ..., z, z̄], ProfileX[g, ..., w, w̄]]
  = ((z-w)(z̄-w̄))^(-α'/2 dot[der[f], der[g]])
```

Type II bosonized exponentials add

```
MWick[expϕb[a, z], expϕf[b, w]] = (z-w)^(-ab)
MWick[expϕf[a, z], expϕf[b, w]] = (z-w)^(-ab)
```

and similarly in the antiholomorphic sector.

### Distributed Wick (`DWick`)

`DWick` is the shared higher-level contraction engine on normal-ordered products.

#### Length-One Reductions

When both inputs have length one, `DWick` reduces to one of four cases:

```
simple × simple:
  DWick[R[a], R[b]] = Wick[R[a], R[b]] or 0

simple × composite:
  DWick[R[a], R[b]] = SWick[R[a], R[b]] R[b] or 0

composite × simple:
  DWick[R[a], R[b]] = R[b] + SWick[R[a], R[b]] or R[b]

composite × composite:
  DWick[R[a], R[b]] = MWick[R[a], R[b]] R[b] or R[b]
```

So `DWick` is not just a sum of deleted-field contractions: in the composite-left cases it acts as a transformation of the right operator.

#### Simple Field vs. Longer Product

When the left input is a single simple field and the right input has length greater than one, `DWick` scans the right product once from left to right:

```python
def DWick_simple(R[a], R[b1, ..., bn]):
    result = 0
    sign = 1
    for i, bi in enumerate([b1, ..., bn]):
        if pairing({Head[a], Head[bi]}) == 1:
            if isComposite(Head[bi]):
                result += sign * SWick[a, bi] * R[b1, ..., bn]
            else:
                result += sign * Wick[a, bi] * R[b1, ..., b̂i, ..., bn]
        sign *= (-1)^(parity[R[a]] * parity[R[bi]])
    return result
```

If the single simple field is on the right instead, the code recycles the same routine via graded symmetry:

```
DWick[Ra, Rb] = (-1)^(parity[Ra] parity[Rb]) DWick[Rb, Ra]
```

for `Rb` of length one and simple.

#### Composite Field vs. Longer Product

When the left input is a single composite field, the algorithm recurses through the right product:

```python
def DWick_composite(R[a], R[b1, rest...]):
    if b1 is simple:
        paired = pairing({Head[a], Head[b1]}) * SWick[a, b1] * DWick(R[a], R[rest...])
        unpaired = R[b1, DWick(R[a], R[rest...])]
        return paired + unpaired
    else:
        factor = MWick[a, b1] if pairing({Head[a], Head[b1]}) else 1
        return factor * R[b1, DWick(R[a], R[rest...])]
```

No extra commuting sign is inserted in this branch; the composite field is effectively moved through and then back to its original side.

---

## Operator Product Expansions

`OPE` is now a two-layer system:

1. `OPE` handles multilinearity, nesting, and the split between collapsable and non-collapsable sectors.
2. `OPEWick` performs the free-field recursion on the collapsable part.

### General Properties

Multilinearity:

```
OPE[a + b, c] = OPE[a, c] + OPE[b, c]
OPE[a, b + c] = OPE[a, b] + OPE[a, c]
OPE[λ a, b]   = λ OPE[a, b]    if λ contains no fields
```

Nested OPEs are evaluated right to left:

```
OPE[Ra, Rb, Rc] = OPE[Ra, OPE[Rb, Rc]]
```

Scalar or zero inputs short-circuit:

```
OPE[..., 0, ...] = 0
OPE[f, g] = f g    if one factor contains no fields
OPE[Ra] = Ra
```

### Splitting Collapsable and Symbolic Sectors

For a normal-ordered product

```
Ra = R[a1, ..., an]
```

`splitCollapsable[Ra]` returns

```
{collapsablePart, restPart, sign}
```

where

- `collapsablePart` contains fields with `isCollapsable[Head[field]] = True`
- `restPart` contains the remaining fields
- `sign` is the product of `regcomm` factors needed to move the collapsable fields past the rest

This allows the code to collapse the free sector while keeping the symbolic or theory-specific sector untouched.

### Free-Field Core (`OPEWick`)

If exactly one input contains collapsable fields, `OPE[Ra, Rb]` delegates directly to `OPEWick[Ra, Rb]`.

If both inputs contain collapsable fields, the code computes

```
{collA, restA, signA} = splitCollapsable[Ra]
{collB, restB, signB} = splitCollapsable[Rb]

opeColl = OPEWick[collA, collB]    (with 1 as identity if one side is empty)
opeRest = OPE[restA, restB]        (again with 1 as identity if needed)

OPE[Ra, Rb] = signA signB multiplyFactors[opeColl, opeRest]
```

So plain `OPE` collapses only the metadata-marked free sector, then multiplies the untouched remainder back in.

### Base Cases Inside `OPEWick`

When both inputs have length one:

```
simple × simple:
  OPEWick[R[a], R[b]] = R[a, b] + pairing(a, b) Wick[R[a], R[b]]

simple × composite:
  OPEWick[R[a], R[b]] = R[a, b] + pairing(a, b) SWick[R[a], R[b]] R[b]

composite × simple:
  OPEWick[R[a], R[b]] = R[a, b] + pairing(a, b) SWick[R[a], R[b]] R[a]

composite × composite:
  OPEWick[R[a], R[b]] = (pairing(a, b) ? MWick[R[a], R[b]] : 1) R[a, b]
```

When the left input has length one and the right input is longer:

```
simple left:
  OPEWick[R[a], Rb] = DWick[R[a], Rb] + R @@ Join[List @@ R[a], List @@ Rb]

composite left:
  OPEWick[R[a], Rb] = R[R[a], DWick[R[a], Rb]]
```

When the left input is longer, recursion peels off the first field:

```
simple first field:
  OPEWick[R[a, rest...], Rb] =
    (-1)^(parity[dropFirstFromR[Ra]] parity[R[a]]) OPEWick[R[rest...], DWick[R[a], Rb]]
    + R[R[a], OPEWick[R[rest...], Rb]]

composite first field:
  OPEWick[R[a, rest...], Rb] =
    R[R[a], OPEWick[R[rest...], DWick[R[a], Rb]]]
```

This is the current recursion that the code memoizes in `$OPEWickCache`.

### Projected OPE (`OPEProjected`)

`OPEProjected[wH, wA]`, `OPEProjectedHolo[wH]`, and `OPEProjectedAntiHolo[wA]` perform projection to target weights by introducing a scaling parameter, reading off the resulting power, and Taylor expanding to the order needed to land at the desired weight.

For one chiral sector the shared logic is:

```python
def project_chiral(OPEexpr, target_weight, ε):
    result = 0
    for term in Expand(OPEexpr):
        scaled = normalizeScalingParameter(term, ε)
        power = Exponent(scaled, ε) /. projectionExponentReplacement
        expansion_order = -power + target_weight
        if expansion_order is a nonnegative integer:
            result += TaylorAtOrderChiral(scaled, expansion_order, 0)
    return result /. ε -> 1
```

The projected OPE code uses the same collapsable split as the unprojected OPE, but then factorizes mixed-chirality collapsable operators into holomorphic and antiholomorphic lists before projecting each chirality separately.

### Type II Flat-Space Specializations

Type II flat space has additional projected-OPE paths:

- If the inputs are made only from `ψ`, `ψt`, `dϕ`, `dϕt`, and bosonized exponentials, plain `OPE` falls straight through to `OPEWick`.
- If `OPEProjected` sees spin fields `S` or `St`, it does not use ordinary Wick recursion. Instead it
  - extracts incoming matter representations,
  - determines total picture and GSO parity,
  - asks `BasisGeneration` for candidate outgoing operators at the target weight,
  - builds compatible tensor structures,
  - attaches symbolic coefficients,
  - and returns an association describing the holomorphic and antiholomorphic projected outputs.

This is the main place where the current Type II algorithm differs from the older purely recursive free-field story.

---

## Taylor Expansion

`TaylorAtOrderHolo`, `TaylorAtOrderAntiHolo`, and `TaylorAtOrder` expand local operators around a chosen point and are used throughout OPE projection, BRST/PCO residue extraction, and bracket projection.

### Purpose

If a field sits away from the expansion point, Taylor expansion rewrites it as a field at the target point together with explicit powers of the coordinate difference. For ordinary derivative fields this has the form

```
f[n, z] -> Σ_k (z-z0)^k / k! f[n+k, z0]
```

The current code applies this logic field-by-field inside a normal-ordered product.

### Partition-Based Algorithm

For `TaylorAtOrderHolo[R[f1, ..., fm], ord, z0]`:

1. Count how many holomorphic fields are expandable, i.e. holomorphic fields not already at `z0`.
2. Compute all ordered partitions of `ord` into that many slots, including zeros:

```
computePartition[ord, length]
```

3. For each partition, walk through the operator from left to right and assign the requested number of added derivatives to the next expandable field.
4. Sum the resulting `R[...]` expressions.

Schematically,

```python
def TaylorAtOrderHolo(R[f1, ..., fm], ord, z0):
    partitions = computePartition(ord, expandable_holo_length)
    result = 0
    for partition in partitions:
        result += R[addHoloDerivatives(fi, ki, z0) or fi]
    return result
```

The antiholomorphic routine is identical with holo replaced by anti-holo.

### Zeroth Order and Scalars

At order zero the Taylor routines still move expandable fields to the target point:

```
TaylorAtOrderHolo[Ra, 0, z0]
```

maps every movable holomorphic field in `Ra` to `z0` with zero extra derivatives.

Scalars are treated as constants:

```
TaylorAtOrderHolo[scalar, 0, z0] = scalar
TaylorAtOrderHolo[scalar, ord > 0, z0] = 0
```

and similarly in the antiholomorphic sector.

### Field-Specific Derivative Rules

The base Taylor module defines the ghost rules:

```
addHoloDerivatives[b[n, z], k, z0] = (z-z0)^k / k! b[n+k, z0]
addHoloDerivatives[c[n, z], k, z0] = (z-z0)^k / k! c[n+k, z0]
```

with the analogous `bt`, `ct` antiholomorphic rules.

Theory-specific Taylor submodules extend this to the actual matter fields in use:

- Bosonic / flat space:
  - `dX`, `dXt`
  - `expX`, `expXHolo`, `expXAntiHolo`
  - `ProfileX`, `ProfileXHolo`, `ProfileXAntiHolo`

- Type II:
  - `η`, `ξ`, `dϕ`, `expϕ*`
  - `ψ`, `ψt`
  - `S`, `St`

For composite exponentials and profiles, the derivative is not just an index shift. The code rewrites the field at the new point times a polynomial in derivative fields:

```
addHoloDerivatives[expX[k, z, z̄], ord, z0]
  = (z-z0)^ord / ord! expX[k, z0, z̄] (expXPoly[k, ord] /. x -> z0)

addHoloDerivatives[ProfileX[f, ders, z, z̄], ord, z0]
  = (z-z0)^ord / ord! ProfileX[f, ders, z0, z̄] (ProfileXPoly[f, ord] /. x -> z0)

addHoloDerivatives[expϕf[a, z], ord, z0]
  = (z-z0)^ord / ord! expϕf[a, z0] (phiPoly[a, ord] /. x -> z0)
```

Spin fields are handled by increasing their explicit derivative count:

```
S[..., der, z] -> (z-z0)^ord / ord! S[..., der + ord, z0]
```

This is the mechanism used later by projected OPEs and by BRST / PCO residue extraction.

---

## String Bracket Computation

`Bracket` and `BracketProjected` operate on local operators represented as `R[...]` or `MultiOp[...]`. The current bracket pipeline is shared across theories at the bosonic level and then extended in Type II by picture-changing logic.

### Overview

1. Build local coordinate maps for the chosen bracket.
2. Place each local operator with the correct Jacobian factors.
3. Construct the required curly-B insertions from the local coordinates and c-ghost content.
4. Apply the combined b-ghost modes to the resulting `MultiOp`.
5. Project the local OPEs to the desired weights, with a factorized path when possible.
6. In Type II, insert and later evaluate the needed PCO zero modes; in effective brackets, compose projected brackets and propagators over all tree nestings.

### Step 1: Local Coordinate Maps and Placement

The bracket-specific submodule provides

```
getLocalCoordinateData[order]
```

which returns

- holomorphic local coordinate maps
- antiholomorphic local coordinate maps
- local variables `w`, `wbar`
- the list of moduli
- replacement rules for the abstract moduli-dependent coordinate symbols

The shared placement code then applies

```
OpAtPos[op, coordHol, coordAntiHol]
```

which dispatches to `RAtPos` or `MultiOpAtPos`.

If `coordHol` and `coordAntiHol` are genuine maps, `mapOp` multiplies each field by the correct Jacobian powers using `weightHolo` and `weightAntiHolo`. If numeric coordinates are given directly, placement skips the Jacobian scaling and only substitutes positions.

### Step 2: Determine Required b-Modes

Before building the curly-B integrand, the code determines how far the b-mode expansion has to go.

`getMinCGhostModding[z0][expr]` scans a local operator for `c` fields:

```python
def getMinCGhostModding(z0, expr):
    min_mode = None
    for field in expr:
        if field is c[n, z]:
            current = 1 - n if z == z0 else 0
            if min_mode is None or current < min_mode:
                min_mode = current
    return min_mode
```

The antiholomorphic routine `getMinCbarGhostModding` does the same for `ct`.

The resulting bound determines the maximal order needed in the local inverse-series expansion used to build the b-ghost insertion.

### Step 3: Construct Curly-B Insertions

For each insertion and each modulus, `createBs`:

1. computes the insertion point `z0 = localCoordinateHol[0]`,
2. inverts the local coordinate map as a truncated series,
3. differentiates the local coordinate with respect to the moduli using the custom `Differential` operator,
4. expands the result around the insertion point,
5. converts powers of `(z-z0)` or `(zbar-z0bar)` into `bmodeHolo[z0][p-1][position]` or `bmodeAntiHolo[z0bar][p-1][position]`.

Schematically,

```python
def createBs(insertion, local_map, moduli):
    min_mode = getMinCGhostModding(z0, insertion)
    max_order = -min_mode + 1
    w_of_z = inverse_series(local_map, max_order)
    coeff_series = series(-Differential(local_map[w], moduli) |_{w=w_of_z})
    return power_to_bmode(coeff_series)
```

`createCurlyB` sums these contributions over all insertions.

### Step 4: b-Ghost Mode Action and Combination

The actual action of `bmodeHolo` and `bmodeAntiHolo` is implemented as a shared helper in `BasisGeneration`.

For a local operator `R[...]`, `bmodeHolo[contourCenter][mode]` scans the product, finds all compatible `c` ghosts, and replaces each one by the corresponding coefficient:

```python
def bmodeHolo(z0, mode, R_operator):
    result = 0
    fermion_number = 0
    for position, field in enumerate(R_operator):
        if field is c[n, z] and mode >= n - 1:
            if z != z0:
                coeff = (-1)^fermion_number (z-z0)^(mode-(n-1)) / (mode-(n-1))!
            elif mode == n - 1:
                coeff = (-1)^fermion_number
            else:
                continue
            result += replace_field_by_scalar(R_operator, position, coeff)
        if field is fermionic:
            fermion_number += 1
    return result
```

The antiholomorphic version is identical with `c` replaced by `ct`.

`actBGhostMode` then distributes these mode actions over `MultiOp[...]`, inserting the usual sign from passing the odd b-mode through earlier local operators:

```
(-1)^(sum of parityOp of earlier entries)
```

Multiple curly-B insertions are combined by `combineCurlyBs`, which wedges the differential-form part through `Wedge` and concatenates the b-mode placeholders. `createCurlyBs` iterates this combination and then sorts the accumulated b-mode list into canonical order, multiplying by the corresponding signature.

Finally,

```
applyCurlyBs[opList, curlyBs, moduliLength]
```

acts with each combined b-mode term on the `MultiOp`, and the bosonic bracket multiplies the result by the overall normalization

```
1 / (-2π i)^(moduliLength/2)
```

together with the sign and factorial factor from `applyCurlyBs`.

### Step 5: Projected Brackets

The unprojected bosonic bracket is

```
Bracket[...] = b0mHold[BracketBosonic[...]]
```

so the final `b0^-` action is intentionally kept abstract until later.

`BracketProjected[..., wH, wA]` then calls the shared `BracketProjection` logic on the unwrapped bracket.

For each local `MultiOp` term, `projectBracketLocalOps` chooses between two paths.

#### Factorized Path

If there are no mixed-chirality local fields, or every mixed-chirality field is marked `Factorizable`, the code uses

```
factorizeMultiOp[MultiOp @@ localOps]
```

to produce

```
{multiOpHolo, multiOpAntiHolo, prefactor}
```

and then computes

```
projectedHolo     = OPEProjectedHolo[wH] @@ holoLocalOps
projectedAntiHolo = OPEProjectedAntiHolo[wA] @@ antiHoloLocalOps
result = prefactor combineProjectedBracketChiral[projectedHolo, projectedAntiHolo]
```

This is the preferred path for flat-space exponentials and profiles.

#### Generic Path

If some mixed-chirality local operator is not factorizable, the code falls back to

```
OPEProjected[wH, wA] @@ localOps
```

and keeps the unsplit local operators together.

`CollapseB0m` later turns the held `b0mHold` into the actual difference of holomorphic and antiholomorphic zero-mode actions.

### Step 6: Type II PCOs and Effective Brackets

Type II extends the bosonic pipeline in two places.

#### Type II Picture-Changing

The unprojected Type II bracket first computes the bosonic bracket, then inserts abstract zero-mode PCO actions:

```
afterHeldActionOfPCOs =
  Nest[actPCObar0Hold,
    Nest[actPCO0Hold, afterApplyingBghosts, numberOfHoloPCOs],
    numberOfAntiHoloPCOs]
```

where the number of needed PCOs is determined from the total input pictures.

During projection, these hold wrappers are stripped, the local OPE is projected through the same shared helper as above, and then the actual PCO actions are applied:

- `actPCOHolo` / `actPCOAntiHolo` on the factorized path
- `actPCO` on the generic path

Each PCO action computes an OPE with each term in `PCO` or `PCObar`, uses `upperBoundSingularity` as a prefilter, and extracts the zeroth-order pole by Taylor expansion.

#### Effective Bracket

`EffectiveBracketHold[fields..., wH, wA]` enumerates all allowed tree-level nestings by:

1. taking integer partitions of the number of external fields, excluding the trivial all-ones partition,
2. assigning field indices to groups of the requested sizes,
3. ordering those groups into valid outer-to-inner nestings,
4. building nested expressions from `BracketHold`, `PropagatorHold`, `ProjectorHold`, and `ProjectorBarHold`.

`EffectiveBracket` then evaluates this symbolic tree sum by the substitutions

```
ProjectorBarHold -> (1 - ProjectorHold)
ProjectorHold[BracketHold[...]] -> CollapseB0m[BracketProjected[...]]
BracketHold[...] -> CollapseB0m[Bracket[...]]
PropagatorHold[q] -> -ApplyPropagator[q]
```

This produces the full tree-level effective bracket while reusing the ordinary bracket, projection, and propagator machinery.

---

## Module Dependencies

The current dependency structure is roughly

```
Symbols
  ↑
NormalOrdering      Operators
  ↑                 ↑
Wick                │
  ↑                 │
Taylor              │
   ↖               ↗
        OPE
         ↑
BasisGeneration
         ↑
Brackets
```

with the following interpretation:

- `Symbols` defines field metadata and the shared predicates used everywhere else.
- `NormalOrdering` uses that metadata to build `R[...]`, parity, and total-weight bookkeeping.
- `Wick` uses `Symbols` and `NormalOrdering`.
- `Operators` handles `MultiOp` and conformal placement.
- `Taylor` uses `Symbols`, `NormalOrdering`, and `Wick`.
- `OPE` depends on `Symbols`, `NormalOrdering`, `Wick`, `Taylor`, and `Operators`.
- `BasisGeneration` provides the shared b-ghost mode action helpers and, in Type II flat space, part of the projected spin-field OPE machinery.
- `Brackets` sits on top of `NormalOrdering`, `Operators`, `BasisGeneration`, `OPE`, and `Taylor`, with theory-specific and bracket-specific submodules supplying BRST currents, PCOs, and local-coordinate data.

Each layer still has theory-specific submodules such as `Bosonic/` and `TypeII/`, and CFT-specific submodules such as `FlatSpace/` and `MinimalModel/`.
