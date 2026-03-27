# Cached Performance Notes for the 5-Spin TypeII FlatSpace `OPEProjected` Case

## Scenario

The stress case is

```wl
OPEProjected[0, 0][
  R[S[{a1, "chiral"}, -1/2, {}, 0, z1]],
  R[S[{a2, "chiral"}, -1/2, {}, 0, z2]],
  R[S[{a3, "chiral"}, -1/2, {}, 0, z3]],
  R[S[{a4, "chiral"}, -1/2, {}, 0, z4]],
  R[S[{a5, "chiral"}, -1/2, {}, 0, z5]]
]
```

All timings below were taken in a fresh TypeII kernel on the current cached implementation.

One important caveat:

- [`OPEProjected`](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m#L1723) first tries the compiled solver.
- For this 5-spin case, the compiled solver does not finish. It finds only `11` independent rows out of the required `16`, exhausts its candidate budget, and returns `$Failed`.
- The public call then falls back to the legacy solver.

So the timings below are a lower bound on the public-call cost before fallback starts. They are still the right timings to study, because the compiled path is where the new sparse/cache machinery is supposed to pay off.

## Executive Summary

- The canonical gamma-product cache worked. Gamma-product construction is now cheap enough to be irrelevant.
- The compiled 5-spin solve is no longer dominated by gamma products or by projected LHS evaluation.
- It is dominated by exact RHS term evaluation inside [`spinProjectionCandidateRows`](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m#L1378).
- Inside that, one single `3`-dummy term is the main offender.
- The compiled solver also appears to have a coverage problem, not just a speed problem: randomized valid candidates still stall at rank `11`, so this is not behaving like a simple coupon-collector process over `16` roughly independent row types.

## Reproduction Tools

The first two recommended fixes now have committed repro scripts:

- [AuditFiveSpinCached.wls](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/AuditFiveSpinCached.wls)
  reproduces the deterministic `800`-candidate rank audit and the randomized valid-candidate comparison for this exact 5-spin case
- [ProfileFiveSpinHeavyTerm.wls](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/ProfileFiveSpinHeavyTerm.wls)
  reproduces the heavy-term descriptor and its per-term timing split on the first deterministic candidate

## Top-Level Breakdown

Measured before fallback:

| Stage | Time | Share of pre-fallback total |
| --- | ---: | ---: |
| [`getOutgoingOperatorsTensors`](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m#L345) | `4.444s` | `3.65%` |
| [`compileSpinProjectionSectorModel`](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m#L977) | `0.059s` | `0.05%` |
| [`solveCompiledSpinProjectionSector`](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m#L1507) | `117.266s` | `96.30%` |
| Pre-fallback total | `121.769s` | `100%` |

At this point the compiled path fails and the public call still has to do more work in the legacy fallback.

## Compiled Solve Breakdown

Inside the `117.266s` compiled solve:

| Stage | Time | Share of compiled solve |
| --- | ---: | ---: |
| [`spinProjectionCandidateRows`](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m#L1378) | `116.021s` | `98.94%` |
| [`spinProjectionProjectInputs`](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m#L823) | `0.567s` | `0.48%` |
| [`spinProjectionConcreteInputs`](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m#L1427) | `0.068s` | `0.06%` |
| [`spinProjectionOperatorAssociation`](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m#L759) | `0.052s` | `0.04%` |
| everything else | `0.558s` | `0.48%` |

This is the first important conclusion:

- the bottleneck is not projected LHS evaluation
- the bottleneck is not output association construction
- the bottleneck is not final linear algebra
- the bottleneck is overwhelmingly the RHS row-generation path

For the `11` candidates that produced accepted rows, the average accepted-candidate costs were:

- LHS projection: about `51.6 ms`
- concrete input construction: about `6.2 ms`
- LHS operator association: about `4.7 ms`

Those numbers are small compared to the row-generation cost below.

## `spinProjectionCandidateRows` Breakdown

Inside [`spinProjectionCandidateRows`](/home/scheinpflug/Github/string-code/StringCode/OPE/TypeII/FlatSpace/FlatSpace.m#L1378):

| Substage | Time | Share of `candidateRows` |
| --- | ---: | ---: |
| term scan | `112.456s` | `96.93%` |
| output-spin-domain pruning | `2.539s` | `2.19%` |
| state-iterator setup | `0.094s` | `0.08%` |
| output-association accumulation | `0.029s` | `0.02%` |
| basis insertion | `0.082s` | `0.07%` |
| other | `0.821s` | `0.71%` |

The second important conclusion is even sharper:

- the current 5-spin compiled path is almost entirely a term-evaluation problem
- support pruning, state iteration, output association, and basis insertion are all small by comparison

Some useful per-try averages:

- `800` candidate-row calls total
- total `candidateRows` time per visited candidate: about `145.0 ms`
- `3864` output states visited total, about `4.83` per candidate
- `12800` active terms scanned total, exactly `16` per candidate on average

That last point matters: even after the current support pruning and term bucketing, each visited candidate still ends up paying for the full `16` active compiled terms on average.

## Term-Level Breakdown

The compiled holomorphic model for this case has:

- `16` coefficient variables
- `1` output family
- `16` compiled terms
- `15` terms with dummy count `1`
- `1` term with dummy count `3`

Measured term-evaluation totals:

| Term bucket | Evaluations | Total time | Time per evaluation |
| --- | ---: | ---: | ---: |
| dummy count `1` | `12000` | `15.521s` | `1.29 ms` |
| dummy count `3` | `800` | `95.825s` | `119.8 ms` |
| all term evaluations | `12800` | `111.346s` | `8.70 ms` |

This is the key bottleneck:

- one single `3`-dummy term consumes about `81.7%` of the entire compiled solve time
- the `15` one-dummy terms together consume only about `13.2%`

So the present 5-spin problem is not “many moderately expensive terms.” It is “one very expensive exact term that is being reevaluated once per candidate.”

## What The Cache Fixed

The canonical gamma-product cache did the intended job.

Measured on the hot rank-3 family:

- cached sweep over all `Binomial[10, 3] = 120` sorted triples: about `0.00068s`
- old uncached builder on the same sweep: about `0.07969s`

That is about a `117x` speedup for the gamma-product construction layer itself.

This is the third important conclusion:

- gamma-product construction is no longer the reason the 5-spin case is slow
- the cache exposed the next bottleneck cleanly
- that next bottleneck is the exact dummy-summed term evaluator wrapped around the cached products

In other words, the problem is not sparse matrix access. The problem is the symbolic/exact scaffolding around repeated term evaluation.

## Why This Is Not A Simple Coupon-Collector Problem

If each candidate were sampling one of `16` reasonably independent row directions, then the row count should grow roughly like coupon collection and randomization should help quickly.

The current data does not look like that.

Deterministic seeded charge-guided search:

- candidate budget: `800`
- candidates visited: `800`
- candidates accepted: `11`
- candidates rejected: `789`
- final rank: `11`

Randomized valid charge-guided sampling:

- sampled `100` random valid candidates
- accepted candidates: `11`
- final rank: `11`
- rank trace: `{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}`

That rank trace is telling:

- random sampling did not uncover a hidden tail of rare missing directions
- it produced the same apparent ceiling at `11`

So the current evidence says:

- candidate ordering is probably not the main issue
- this is not well modeled as coupon collection over `16` sparse row types
- the compiled candidate-to-row map appears strongly degenerate under the current evaluator

That could mean one of two things:

- the compiled path is not exploring the right row space
- the compiled row construction is collapsing distinct candidates onto the same `11` directions

Either way, this is a coverage problem first and a search-heuristic problem second.

## Current Diagnosis

The cached compiled path now has two separate problems.

### 1. Coverage problem

The compiled solver is not reaching the required rank `16`. At the moment it appears to plateau at `11`, even under randomized valid charge-guided sampling.

### 2. Speed problem

Each candidate is still too expensive because the 3-dummy term takes about `119.8 ms` every time it is evaluated. Even if candidate selection improved, this term would still dominate wall clock.

These two problems should not be conflated. A faster compiled path is still not enough if it cannot span the row space. Better candidate ordering is also not enough if each candidate remains expensive.

## Recommended Fixes

### 1. Audit rank reachability before more micro-optimization

This should be the next diagnostic step.

The goal is to answer a simple question:

- are the missing `5` directions reachable at all with the current compiled row construction?

Recommended audit:

- run larger randomized valid candidate samples
- record exact pivot positions or row signatures as rank grows
- compare deterministic seeded order against randomized order
- check whether any candidate ever produces a new direction after rank `11`

If the ceiling is real, then the compiled path has a structural coverage bug. In that case, more candidate shuffling will not solve the problem.

### 2. Profile the 3-dummy term one level deeper

This is the main speed target.

The current note identifies the hot term, but not yet which subpiece inside that term is dominant. The next profiling pass should split its `119.8 ms` into:

- dummy-loop enumeration cost
- per-tuple gamma-entry or bilinear lookup cost
- exact multiplication cost
- exact summation cost
- any remaining descriptor-resolution overhead

That will tell us whether the next win is:

- stronger caching of scalar/bilinear values
- less exact arithmetic inside the dummy loop
- or a fuller term-lowering rewrite

### 3. Push caching one layer closer to the scalar value

The current cache stores concrete gamma-product matrices. That was necessary and correct, but it still leaves the term evaluator doing repeated scalar extraction and exact accumulation.

The next low-risk cache target is not the fully contracted term kernel yet. It is one layer lower:

- cache repeated scalar matrix elements or bilinear values for concrete tuples that recur inside the hot term

That keeps the design local while attacking the remaining repeated work directly.

### 4. Only revisit candidate heuristics after the reachability audit

There may still be value in better candidate ordering, but it should not be the lead fix now.

If the missing directions are reachable, then support-aware candidate scoring may help.

If the missing directions are not reachable under the current compiled row map, then candidate heuristics are a distraction.

## Bottom Line

The cache succeeded. The 5-spin case is still slow because the problem has moved.

What remains is:

- a likely rank-reachability issue that caps the compiled solve at `11/16`
- and a single extremely expensive 3-dummy exact term that dominates per-candidate time

Those are the two issues that now deserve attention. Sparse gamma construction is no longer the one to chase.
