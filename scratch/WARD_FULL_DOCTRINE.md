# DOCTRINE — prove IsEllSequence (normEDS b c d)  [the open Mathlib TODO]

## Goal
`∀ m n r : ℤ, W(m+n)W(m-n)W(r)² = W(m+r)W(m-r)W(n)² − W(n+r)W(n-r)W(m)²` for W = normEDS b c d,
any CommRing R. Unlocks the keystone EDS-core doubling + addition → nsmul_eq_zero_iff_ΨSq_eval.

## What is PROVEN (base, 0 axioms)
- `normEDS_adjacent_somos` = E(m,2,1) for all m (since W(1)=1,W(2)=b,W(3)=c). The induction BASE CASE.
- Universal-ring + map_normEDS transport machinery (reusable for the whole proof).
- complEDS machinery (Mathlib) handles the IsDivSequence half; IsEllSequence is the hard half.

## CAS-established NEGATIVE results (rule out the easy routes)
- E(m,n,1) for n≥3 is NOT in the ideal of adjacent Somos at any finite radius (r≤4), EVEN with the
  curve relation incorporated AND even after denominator-clearing by W(m±1). The EDS satisfies GLOBAL
  relations beyond any local Somos set — Ward's theorem is not a finite cofactor certificate.
- Therefore: NO local Gröbner/linear_combination proof. Needs a genuine induction using the DEFINING
  recurrence (normEDS_even/odd from base values), and the double-index W(m±n) makes it a 2-index problem.

## Candidate avenues (ranked, to refine with ChatGPT rounds)
(a) **r=1 reduction + induction on n.** First prove E(m,n,1) ∀m,n (the "addition formula"); then reduce
    general E(m,n,r) to r=1 by a transfer/symmetry. Induction on n via the recurrence; the step must
    handle W(m±n) for symbolic m (the crux).
(b) **Elliptic-net / Stange framework.** E is the 1-dim elliptic net relation; Stange's recurrence gives
    a clean 2D induction. Possibly the most formalization-friendly (explicit recurrence).
(c) **Universal-ring + σ-function transport.** Prove over MvPolynomial ℤ (domain), via the Weierstrass-σ
    3-term identity pulled back algebraically. Likely needs analytic σ — probably NOT Lean-friendly.
(d) **complEDS-based.** Leverage Mathlib's complement-sequence identities (complEDS_even/odd) — check if
    they shorten the E-relation, not just divisibility.

## Method note (Xiang 2026-06-22)
Hard theorem → DRIVE myself first + go several ROUNDS with ChatGPT (parallel, verify-don't-transcribe).
This is the right ChatGPT use (not the serial-wait anti-pattern of lesson-0067). Year-long horizon, 遇山开山.

## Terminal condition
`IsEllSequence (normEDS b c d)` proven, 0 custom axioms, #print axioms standard-only.

## PROGRESS 2026-06-22 (Step 1 DONE)
- **Step 1 PROVEN** (scratch/WardEllSequence.lean, committed): IsEllSequence reduces to 2-var AddRel.
  CAS-verified exact reduction (8 sign combos, unique match): `IsEllSequence(m,n,r) = -W(n)²·AddRel(m,r)
  + W(m)²·AddRel(n,r) + W(r)²·AddRel(m,n)`. `isEllSequence_of_addRel` proven (pure linear_combination, no
  induction, no W(1)=1 needed). The Mathlib TODO now = ONE sorry: `normEDS_addRel`.
- AddRel(normEDS,m,n) numerically CONFIRMED true for all tested m,n (it IS the addition formula).
- **AddRel def**: `W(m+n)W(m-n) = W(m+1)W(m-1)W(n)² − W(n+1)W(n-1)W(m)²` (= IsEllSequence at r=1, W(1)=1).

## Step 2 PLAN (normEDS_addRel by gap induction on n)
Predicate P(n) := ∀ m, AddRel (normEDS …) m n.  Prove via normEDSRec (the doubling recursion on n):
- Base: n=0 (W(0)=0 trivial), n=1 (B(1)=W(2)W(0)=0 trivial), n=2 (= normEDS_adjacent_somos, DONE), n=3,4.
- **Even gap step** (P(2k) from P(k-2..k+2)): the tautology `W(m)²·S(m,2n) = S(m+n,n)·S(m-n,n)` (S(a,b):=W(a+b)W(a-b)),
  substitute AddRel at centers (m+n,n),(m-n,n) and gaps (m,n-1),(m,n),(m,n+1), the mixed product
  B(m+n)B(m-n)=S(m,n+1)S(m,n-1), then `normEDS_even`/`normEDS_odd` for W(2n),W(2n±1); get W(m)²·AddRel(m,2n)=0,
  cancel W(m)² over the universal domain, transport via map_normEDS.  [VERIFYING this identity via CAS now.]
- **Odd gap step** (P(2k+1)): analogous.
- Cofactors for the linear_combination: sympy Gröbner (same machinery as WardSomos oddStep/evenStepScaled).
- Universal ring MvPolynomial (Fin 3) ℤ for the W(m)² (and any b) cancellation; map_normEDS transport.

## Collaboration note
Step 1 reduction came from a ChatGPT round (its signs were WRONG; I CAS-corrected to -,+,+). Verify-don't-transcribe
caught it. This is the right ChatGPT use for a hard theorem (Xiang 06-22): drive + verify + iterate rounds.
