# DOCTRINE — Mazur keystone differential-addition cert + wiring

**Goal (one sentence):** Discharge `xPair_double_and_diffAddOrInf_EDS_core` (KeystoneLadder.lean L1009) — the Mazur |T|≤16 keystone — by landing the diff-add cert 0-sorry, its SameP1 wiring, and the two nonzero conjuncts.

## Avenues (ranked)

- **(a) Cofactors → encode the 2 numerator sat lemmas.** ODD verified (dm2, expand(G−Σcof·rel)=0). EVEN: extract locally via dm2's proven lex-Groebner-lift method (don't wait on dm1). Encode `Φ_two_mul_add_one_sat_even/odd` via `linear_combination` + norm-simp (mirror KeystoneDoublingCert sat lemmas). Integer cofactors if GF(3) membership holds; else carry `(3:R)≠0`.
  - Terminal success: `KeystoneDiffAddCert.lean` builds 0-sorry/0-custom-axiom.
- **(b) Wire dm3's `xPair_diffAdd_sameP1`** into KeystoneSameP1.lean (compiles once (a) lands). Isolates `hΦinf` (δ=0 → Φ(2m+1).eval≠0).
  - Terminal success: wiring lemma builds, depends only on `hΦinf` + cert.
- **(c) Nonzero/coprimality (deepest).** `gcd(φ_n, ψ_n²)=1` from Δ≠0 → discharge `hΦinf` + the core's two `xPair(2m)≠0`, `xPair(2m+1)≠0` conjuncts. NON-circular (cannot use `xPair_ne_zero_of_isElliptic`). dm4 + SEAM-1 (separability).
- **(d) Final assembly.** Derive h4/hψ_ne/hc3 from `[W.IsElliptic]` (may need char≠2,3); discharge the L1009 sorry wiring (a)(b)(c).

## Fallbacks
- Integer cofactors impossible (GF(3) fails) → carry `(3:R)≠0` / `CharZero` on the cert + cancel in `Φ_two_mul_add_one`.
- Coprimality (c) intractable directly → keep `hΦinf`/nonzeros as explicit hypotheses on the keystone, defer to SEAM-1.

## polyrith is DEAD (Mathlib service shut down) — literal cofactors mandatory.
