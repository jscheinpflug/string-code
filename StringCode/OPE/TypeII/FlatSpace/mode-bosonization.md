 Ground state (recap)                                                                                                                                                         
                                                                                                                                                                               
  In the charge basis (5 free bosons H^1...H^5), the ground state is:                                                                                                          
                                                                                                                                                                               
  S_α(z) → cocycle · e^{i(qφ + s_α · H)(z)}                                                                                                                                    
                                                                                                                                                                               
  where s_α ∈ {±1/2}^5.                                                                                                                                                        

  Single fermion mode ψ^a_{-n} acting on S_α

  The fermion in the charge basis is ψ^a(z) = e^{iv_a·H(z)} where v_a = ±e_i (the 10 vector weights). The OPE around the spin field is:

  e^{iv_a·H(w)} · e^{is·H(z)} = cocycle(v_a, s) · (w-z)^{v_a·s} · e^{i(v_a+s)·H(z)} · Σ_{k≥0} P_k (w-z)^k

  The mode ψ^a_{-n} extracts the coefficient of (w-z)^{n-1/2} from this, so it picks up P_m with:

  - m = n when v_a · s = -1/2 (the "aligned" case)
  - m = n-1 when v_a · s = +1/2 (the "anti-aligned" case)

  The P_m are coefficients of exp(Σ_{k≥1} t^k · iv_a·∂^kH / k!):

  ┌─────┬───────────────────────────────────────────────────┐
  │  m  │                        P_m                        │
  ├─────┼───────────────────────────────────────────────────┤
  │ 0   │ 1                                                 │
  ├─────┼───────────────────────────────────────────────────┤
  │ 1   │ iv_a·∂H                                           │
  ├─────┼───────────────────────────────────────────────────┤
  │ 2   │ iv_a·∂²H/2 + (iv_a·∂H)²/2                         │
  ├─────┼───────────────────────────────────────────────────┤
  │ 3   │ iv_a·∂³H/6 + (iv_a·∂H)(iv_a·∂²H)/2 + (iv_a·∂H)³/6 │
  └─────┴───────────────────────────────────────────────────┘

  Since v_a = ±e_i, each iv_a·∂^kH simplifies to ±i · ∂^kH^i = ±i · dH[i, k-1, z] in the code's notation.

  So the dictionary entry is:

  ψ^a_{-n} S_α(z)  →  cocycle(v_a, s) · P_m · expH[{q, s+v_a}, z]

  Concrete examples

  Zero mode (n=0):
  - Aligned (v·s = -1/2): P_0 = 1, so ψ^a_0 |s⟩ = cocycle · e^{i(s+v_a)·H} — just shifts the charge (gamma matrix action)
  - Anti-aligned (v·s = +1/2): m = -1, so ψ^a_0 |s⟩ = 0 — annihilated

  First excitation (n=1):
  - Aligned: P_1 = iv_a·∂H, so ψ^a_{-1} |s⟩ → cocycle · (iv_a·∂H) · e^{i(s+v_a)·H} — exponential with one dH factor
  - Anti-aligned: P_0 = 1, so ψ^a_{-1} |s⟩ → cocycle · e^{i(s+v_a)·H} — just a pure exponential (no derivatives!)

  Relation to existing code

  The P_m polynomials are closely related to bosonizedExponentialDerivative. Specifically:

  P_m = (1/m!) × bosonizedExponentialDerivative[v_a_charges, m, z, dH, expH] / expH[v_a_charges, z]

  i.e., take the m-th derivative of the bosonized exponential, strip the exponential factor, and divide by m!. The existing Bell polynomial / Faà di Bruno machinery in the
  code computes the numerator.

  Multiple modes

  For multiple modes ψ^{a_1}{-n_1} ψ^{a_2}{-n_2} ... S_α, you'd need to apply them iteratively. After the first mode, the state is P_m · e^{iQ_1·H} where Q_1 = s + v_{a_1}.
  The second mode OPEs with both the dH polynomial and the exponential, so you get additional Wick contractions between ψ^{a_2} and the dH factors from the first step. This
  gets progressively more involved.

  Key structural observation

  The bosonized excited spin field always has the form:

  (polynomial in dH's) × expH[{q, s + Σ v_{a_i}}, z]

  The exponential part just carries the total shifted charge. All the "excitation information" lives in the polynomial prefactor.


  ● Got it — glad the dictionary was useful. To summarize the key takeaway:
                                                                                                                                                                               
  The bosonized excited spin field is always (polynomial in dH) × expH[shifted charge], where the polynomial comes from the Schur/Bell polynomial expansion of the OPE, and the
   shift depends on whether each mode is aligned (v·s = -1/2) or anti-aligned (v·s = +1/2) with the ground state spin vector.                                                  
                                                                                                                                                                               
  If you ever want to implement this later, the existing bosonizedExponentialDerivative machinery already computes the Bell polynomials — you'd just need to divide by m! to   
  get the OPE coefficients P_m.                                                                                                                                                
                                                                                                                                                                                          