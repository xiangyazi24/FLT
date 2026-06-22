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

## Step 2 even-step: ChatGPT sketch INCOMPLETE (CAS-caught), refining
- CAS-verified: the n→2n even step does NOT close with ChatGPT's 5 AddRel hyps. After substituting
  S(m±n,n) via AddRel, the product has CROSS terms `B(m+n)·W(m-n)²` + `W(m+n)²·B(m-n)` that the 5 hyps
  cannot reduce (B(m+n)=W(m+n+1)W(m+n-1) is a SAME-center product; the hyps only give MIXED-center
  products like W(m+n+1)W(m-n-1)). Gröbner leaves 5 residual terms with p1·pm1 and q².
- The naive n→n+1 step also fails: S(m,n+1),S(m,n),S(m,n-1) satisfy no simple linear recurrence (EDS nonlinear).
- This is the genuine Ward-induction difficulty (why it's the open TODO). Correct step needs the right finite
  instance set — round 2 with ChatGPT in flight (asked for the exact Shipsey/Ward step identity + the precise
  ideal-membership instances). I CAS-verify everything before building (caught ChatGPT's sign error + this gap).
- Step 1 (3→2 reduction) is SOLID and committed — the genuine structural breakthrough that halves the problem.

## Round 2 (companion-induction) — structure SOUND, step still open
- ChatGPT round 2 (self-corrected, removed the bad even-step): carry a COMPANION OffRel(k,m) alongside
  GapRel(k,m)=AddRel, induct on gap k STEP-BY-STEP (k→k+1) via (G_k,H_k)⟹(G_{k+1},H_{k+1}). Cites
  van der Poorten–Swart (Somos-4 ⟹ all larger-gap relations).
  · GapRel(k,m): W(m+k)W(m-k) = W(k)²B(m) − B(k)W(m)²,  B(i):=W(i+1)W(i-1).
  · OffRel(k,m): W(2)W(m+k+1)W(m-k) = W(m+2)W(m-1)W(k+1)W(k) − W(k+2)W(k-1)W(m+1)W(m).
  · BOTH numerically VERIFIED to hold for normEDS (all tested k,m). The two driving tautologies are
    genuine regroupings (verified by hand).
- BUT the G-step is NOT a clean formal identity: `H_k(m)·H_k(m-1) − W(2)²·G_{k+1}·G_k` ≠ 0 in free W
  (8-term residual), and that residual does NOT reduce mod {Somos_m, Somos_k} (6 terms remain). So
  ChatGPT's "follows after cancellation" glosses a real gap (its 3rd imprecision; all CAS-caught).
- OPEN: the exact finite relation package that closes the k→k+1 step. Likely needs OffRel/Somos at more
  indices, OR the full Stange 4-term recurrence (s general), OR the diagonal (m=±k) handling interwoven.
  This is the genuine Ward core — the long grind. Step 1 (the 3→2 reduction) remains the solid won ground.

## *** BREAKTHROUGH (round-3 patch, CAS-verified): Ward path is now CONCRETE ***
After feeding ChatGPT the exact 8-term residual, it gave the correct closure (verify-don't-transcribe:
its first 4 attempts were wrong; this one CAS-checks). The whole Ward proof reduces to adjacent Somos +
clean inductions. Verified pieces:
1. **Residual decomposition (FORMAL identity, free W — CAS-exact):**
   R = K₀²K₁²M₁M₋₁·Somos_m + M₀·(K₂·T_{k,m} − K₁²M₁M₀M₋₁·Somos_k),  so R ∈ ⟨Somos_m, Somos_k, T_{k,m}⟩.
2. **Double-off relation** T_{k,m} := N_k·D_m − N_m·D_k = 0, where
   N_n := W(n+2)W(n-1)² + W(n+1)²W(n-2) + b²W(n)³,  D_n := W(n+1)W(n)W(n-1).
   This factors through the **single-index** relation N_n = λ·D_n (λ = (d+b⁴)/c, the Somos-4 conserved quantity).
3. **Conservation step is Somos-reducible (CAS, remainder 0):**
   N_{n+1}·D_n − N_n·D_{n+1} = (−W(n)·W(n+1)³)·adjSomos@n + (W(n)³·W(n+1))·adjSomos@(n+1).
   ⟹ N_n/D_n is index-independent ⟹ N_n = λD_n by a trivial induction (conservation + base n=2).
CHAIN: normEDS_adjacent_somos (DONE) → conservation lemma (clean linear_combination, cofactors above)
 → N_n=λD_n (induction) → T_{k,m}=0 → residual R=0 (decomposition) → G-step (AddRel k+1) → AddRel (gap
 induction) → IsEllSequence (Step 1, DONE).  Remaining build: conservation lemma, single-index induction,
 G-step + H-step assembly (H-step needs its own residual analysis, likely closes the same way).
This turns the open Mathlib TODO into a concrete mechanizable build — all over adjacent Somos + clean inductions.

---

## VERIFIED 2026-06-22 — OffRel form + full G-step cofactors (sympy, free W, exact 0)

**OffRel closed form (CAS-confirmed at many (k,m) on a generic EDS, b=2,c=3,d=5):**
```
V_k(m) := W(2)·W(m+k+1)·W(m-k)
        = W(m+2)W(m-1)·W(k+1)W(k)  −  W(k+2)W(k-1)·W(m+1)W(m)
```

**G-step (multiplied form), cancellation factor b²·U_k(m) = W(2)²·W(m+k)W(m-k):**
```
b²·U_k(m)·( U_{k+1}(m) − Gkp1 )  =  Σ cofactor · hyp   [sympy expand = 0, with combined symbols]
```
where U_{k+1}(m)=W(m+k+1)W(m-k-1), Gkp1 = W(m+1)W(m-1)·W(k+1)² − W(k+2)W(k)·W(m)², and:
| hyp (=0 on EDS)                                  | cofactor                                  |
|--------------------------------------------------|-------------------------------------------|
| GapRel(k,m):  U_k − Gk                            | −b²·Gkp1                                   |
| OffRel(k,m):  W(2)W(m+k+1)W(m-k) − Hkm            | b·W(m+k)·W(m-k-1)                          |
| OffRel(k,m-1): W(2)W(m+k)W(m-k-1) − Hk,m-1        | Hkm = W(m+2)W(m-1)W(k+1)W(k) − W(k+2)W(k-1)W(m+1)W(m) |
| Somos@m:  W(m+2)W(m-2) − (b²W(m+1)W(m-1)−cW(m)²)  | W(k)²W(k+1)²·W(m+1)W(m-1)                  |
| Somos@k:  W(k+2)W(k-2) − (b²W(k+1)W(k-1)−cW(k)²)  | −W(m)²W(k+1)²·W(m+1)W(m-1)                 |
| Trel:  N_k D_m − N_m D_k                          | W(m)·W(k+2)                                |

Residual sub-identity (local only, CAS=0):
`Hkm·Hk,m-1 − b²·Gk·Gkp1 = W(k)²W(k+1)²W(m+1)W(m-1)·Somos@m + W(m)W(k+2)·Trel − W(m)²W(k+1)²W(m+1)W(m-1)·Somos@k`.

H-step (OffRel(k+1)) + base cases k=0,1,2: pending (ChatGPT dm1 + own search).
