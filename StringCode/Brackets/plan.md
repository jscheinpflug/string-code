# Effective bracket

## Task Description
- Task: Define `EffectiveBracket[SF1, ..., SFn]` defined (as a public method, with possibly private helpers) via the following combinatorial procedure:

- Compute `IntegerPartitions[n]` (excluding the partition into all 1s) and for each partition `{n1,...,nk}` assign `SFn1, ..., SFnk`.
- Now, compute all nestings of the various partitions into each other
- Example for partition of 5 of the form {3,2}, and one of the assignments like `SFn1 ,SFn3, SFn4` and `SFn2, SFn5` give `ProjectorHold[BracketHold[SFn2, SFn5, PropagatorHold[ProjectorBarHold@BracketHold[SFn1, SFn3, SFn4]]]]` (which is 3 in 2) and `ProjectorHold[BracketHold[SFn1, SFn3, SFn4, PropagatorHold[ProjectorBarHold@BracketHold[SFn2, SFn5]]]]` (which is 2 in 3)
- Example for partition of 4 of the form {2,2}: `ProjectorHold[BracketHold[SFn1, SFn2], PropagatorHold[ProjectorBarHold@BracketHold[SFn3,SFn4]]]`
- Example for partition of 4 of the form {3,1}: `ProjectorHold[BracketHold[SFn3, PropagatorHold[ProjectorBarHold@BrackeHold[SFn1,SFn2,SFn4]]]]`
- Example for partition of 4 of the form {2,1,1}: `ProjectorHold[BracketHold[SF1, PropagatorHold[ProjectorBarHold@BracketHold[SF2,PropagatorHold@ProjectorBarHold@BracketHold[SF3,SF4]]]]`
- Example for partition of 4 of the form {4}: `ProjectorHold[BracketHold[SF1,SF2,SF3,SF4]]`
- In the examples above, there are of course other combinations where you have different groupings of `SFni`
- It might help you that each of these combinations corresponds to a tree, with `n`-valent vertices where `n` is the length of a grouping, joined with lines (propagators) - and this is just dressed by projectors: internal line gets projectorBar, outgoing line gets projector.
- One is to build a helper method with `BracketHold`, `PropagatorHold[q]`, `ProjectorHold` such that after adding all the terms together `BracketHold` is substituted for `Bracket`, `PropagatorHold` for `ApplyPropagator` and `ProjectorHold` of `Bracket` is `ApplyPropagator` on `Bracket`. All of these should be (multi)linear so that automatic simplifications happen before the substitution.

---

## Implementation (Completed)

### Public API
```mathematica
EffectiveBracket[SF1, ..., SFn]
```
Computes the sum over all tree-level diagrams built from brackets connected by propagators.

### Algorithm
```
EffectiveBracket[SF1, ..., SFn] =
  Σ (over partitions P of n, excluding {1,...,1})
    Σ (over assignments of SFs to partition groups)
      Σ (over tree nestings)
        buildTerm[...]
```

### Helper Functions (Private)
1. **`getPartitions[n]`** - Returns `IntegerPartitions[n]` excluding the all-1s partition
2. **`assignToGroups[items, sizes]`** - Generates all ways to assign n items to k groups of specified sizes
3. **`generateNestings[groups]`** - For groups of size ≥2, generates all tree nestings (each can be outer); singletons attach directly to outer bracket
4. **`buildPropagatorChain[groups, qs]`** - Builds nested `PropagatorHold[qi][ProjectorBarHold[inner]]` structure
5. **`buildHoldTerm[outer, inner, singletons]`** - Constructs `ProjectorHold[BracketHold[...]]` term

### Output Format
`EffectiveBracket` returns symbolic expressions using only:
- `BracketHold[...]`
- `PropagatorHold[q][...]`
- `ProjectorHold[...]`
- `ProjectorBarHold[...]`

**No substitution is performed** - user handles conversion to `Bracket`, `ApplyPropagator`, `BracketProjected` separately.

### Key Design Decisions
- **Unique q per propagator**: Each internal propagator gets a unique symbol via `Unique["q"]`
- **Singletons create chain levels**: Partition {2,1,1} means 2-bracket inside 2-bracket inside 2-bracket (not singletons attaching to outer)
- **Tree nesting**: Groups form a linear chain; valid orderings have innermost group with ≥2 elements
- **Multilinearity**: All Hold symbols and `EffectiveBracket` itself distribute over sums and factor out field-free constants

### Term Counts

| n | Partition | Assignments | Orderings | Terms |
|---|-----------|-------------|-----------|-------|
| 3 | {3} | 1 | 1 | 1 |
| 3 | {2,1} | 3 | 1 | 3 |
| **3** | **Total** | | | **4** |
| 4 | {4} | 1 | 1 | 1 |
| 4 | {3,1} | 4 | 1 | 4 |
| 4 | {2,2} | 3 | 2 | 6 |
| 4 | {2,1,1} | 6 | 2 | 12 |
| **4** | **Total** | | | **23** |

**Example {2,1,1}**: `ProjectorHold[BracketHold[SF1, PropagatorHold[q1][ProjectorBarHold[BracketHold[SF2, PropagatorHold[q2][ProjectorBarHold[BracketHold[SF3, SF4]]]]]]]]`

### Tree Structure Examples

**n=3, partition {2,1}** (3 assignments):
```
    [P]
     |
  [Bracket]
   /      \
 SF3    [Prop(Pbar)]
            |
        [Bracket]
         /     \
       SF1    SF2
```

**n=4, partition {2,2}** (3 assignments × 2 nestings = 6 terms):
```
    [P]                          [P]
     |                            |
  [Bracket]                   [Bracket]
   /   |   \                   /   |   \
 SF1  SF2  [Prop(Pbar)]      SF3  SF4  [Prop(Pbar)]
              |                          |
          [Bracket]                  [Bracket]
           /     \                    /     \
         SF3    SF4                 SF1    SF2
```

**n=6, partition {2,2,2}** (multiple propagators with unique q's):
```
ProjectorHold[BracketHold[SF1, SF2,
  PropagatorHold[q1][... - ProjectorHold[BracketHold[SF3, SF4,
    PropagatorHold[q2][... - ProjectorHold[BracketHold[SF5, SF6]]]]]]]]
```

### Resolved issues:
- **Fixed**: `assignToGroups` now works with positional indices (`Range[n]`) instead of field values. This prevents `Subsets`/`Complement`/`Permutations` from collapsing duplicate elements. Indices are mapped to actual fields only when building the final expression in `buildHoldTerm`.