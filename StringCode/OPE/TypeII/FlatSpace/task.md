# Implement bosonization of free fermion sector

## Background
- Currently, in `FlatSpace.m` OPE code, we are trying to compute OPE in free fermion sector, with spin fields included
- The idea is to use bosonization, which turns the OPE into free field computed by OPEWick
- To do this, we want to write out all tensor structures and operators that can appear in this OPE (`TensorStructures.m`), bosonize both sides and match coefficients with indices plugged in for (randomly)
- What is missing is the bosonization step and I want you to focus on this
    - We are missing the bosonized fields themselves i.e. the `expH` and `dH` free bosons. These should be implemented pretty much like `expH` and `dX`, but with alpha' = 2 convention AND now instead of momentum like `k`, one should have SIX numbers in an array (the 'spins'). The basic procedure is explained in `./spin-field.png`.
- We have a prototype, which handles bosonization of `psi` and a simple spin field `S` (with no modes!). We know how to bosonize some specific combinations of `psi` and then need to convert to the canonical basis with index `mu` via matrix `M` as shown in `./spinfield cocycles.wlnb` or `cocycle-tests.wlnb`.
- We also have a first attempt by a colleague `SpinFields.wl`, which tries to perform some of the bosonization. The colleague defines H1,...,H5 but I think we should also treat the `phi` charge together with the H's in a single boson `dH` (or antiholo `dHt`), which would carry an index, which could take six values like `dH[1, ...], ..., dH[6, ...]` similar to `dX[mu,...]`.
- In `SpinFields.wl` spinFieldHoloExp function hardcodes the transformation, this should instead be handled via the change of basis matrix like in `spinfield cocycles.wlnb`. They also introduce these `Sb` fields, for us those are simply the `expH` with index being a length 6 vector. The main takeover is that bosonization should not be hardcoded.
- Note that when bosonizing, we have to take into account cocycle phases, see `spinfield cocycles.wlnb`. We create bosons but they have phases when they contract. Moreover, importantly, when you bosonize a normal ordered product `R`, you have to multiply the result on cocycle phase between every tuples of operators in that normal-ordered product to account for their statistics.

## Task
- Add `dH, dHt, expH` bosons with the properties I described
- These are bosonic free fields, with Wick contraction rules defined with cocycles of `spinfields cocycles.wlnb`
- Add bosonization rules (`Bosonize` function) for `psi, psit, S, St` (and exponentials - expphi just becomes expH with the first entry in vector nontrivial; and the charge of spin fields also becomes that index!)
- Note that this bosonization should work only when the vector index `mu` is an actual number 1, ..., 10 and the spinor index `alpha` let's say is replaced by 5 length vector (from chiral or antichiral spin list). It is important that for the `mu` index, there is a nontrivial change of basis matrix `M`: `psi^mu = M^mu_a psi^a`, where `psi^a` is the basis we know how to bosonize.
- For now just handle the case where `S, St` have empty modes
- Add bosonization rules for normal-ordered products of these (`Bosonize` overloaded)
- After you are done, reproduce the definitions of gamma matrices of `cocycle-tests.wlnb` and show that OPE of psi-S operators yields the right gammas like in that file `cocycle-tests.wlnb` (there is a subtlety that one of the gammas we are comparing with has index down, so we gotta raise if by M^{-1}: if we got gamma_a psi^a, then we need gamma_mu psi^mu = gamma_a M^a_mu M^mu_a psi^a, so gamma_mu = gamma_a M^a_mu).
- Feel free to include the same checks of associativity etc. as in that file, but I warn you - be faithful to the bosonization logic and notation of this task, those other files are just some half-baked prototypes and you shouldn't take their notation too seriously, I think I unambiguously specified it here.
- Ask questions where the above task is ambiguous and/or you need clarification.