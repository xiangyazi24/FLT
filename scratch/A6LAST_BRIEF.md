# A6 LAST SEAM — close the single remaining sorry in A6TorsionFinite.lean

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2. Build with `lake build`/`lake env lean` here
(NEVER local mini build; edit ONLY scratch/A6TorsionFinite.lean + scratch/A6HeightProto.lean if a
helper must be exposed; do NOT touch built files).

## STATE (verified by fresh grep — file compiles, EXIT 0)
scratch/A6TorsionFinite.lean has EXACTLY 1 `sorry` left, 0 axioms, at the theorem
`dup_projective_height_lower_from_raw_gcd` (~L562-574). Everything else is CLOSED, including:
- `xRep_two_nsmul_same_dup` (EC duplication), the primitive [num:den] degree-4 bridge
- the two PROVEN rational homogeneous Bezout certificates `dup_bezoutX_Q`, `dup_bezoutZ_Q`
  (Δ²·X⁷ = UX·F + VX·G  and  Δ²·Z⁷ = UZ·F + VZ·G, by ring)
- the general `HomogeneousBezoutCertificate.gcd_dvd_D_natAbs_of_natAbs_coprime`
- the proven raw bound `dup_projective_height_lower_height_api_seam` (in A6HeightProto.lean), bound to
  `hraw` in the goal context.

## CLOSE THIS ONE SORRY
Goal: ∃ C ≥ 0, ∀ x y : P1Q, P1Q.SameQ y (dupNumH E x.X x.Z) (dupDenH E x.X x.Z) →
        P1Q.logHeight y ≥ 4 * P1Q.logHeight x − C.

The bridge (this is the "denominator-clearing + true-height comparison" layer):
1. For a primitive P1Q `x`, `naiveLogHeightP1Q (x.X:ℚ) (x.Z:ℚ) = P1Q.logHeight x` (primitive ⇒ the
   ℚ-cast pair height equals the integer primitive height). Prove/locate this equality lemma.
2. `hraw` gives `naiveLogHeightP1Q (dupNumH E x.X x.Z) (dupDenH E x.X x.Z) ≥ 4·naiveLogHeightP1Q (x.X)(x.Z) − C0`.
3. `y` is the PRIMITIVE rep of the projective point [dupNumH : dupDenH] (which may be ℚ-valued since the
   b-invariants are rational). Relate `P1Q.logHeight y` to `naiveLogHeightP1Q (dupNumH..)(dupDenH..)`:
   clearing the common denominator does not change the projective point, and reducing to primitive
   divides out gcd; by the proven gcd∣Δ² (use `gcd_dvd_D...` instantiated with `dup_bezoutX_Q`/`_Z_Q`),
   the reduction loses at most `log|Δ²| = 2 log|Δ|`. So `P1Q.logHeight y ≥ naiveLogHeightP1Q(F,G) − 2 log|Δ|`.
   Handle the degenerate G=0 (2-torsion → [F:0]=[1:0], P1Q.logHeight = 0; gcd(F,0)=|F|∣Δ²).
4. Combine: `P1Q.logHeight y ≥ 4·P1Q.logHeight x − (C0 + 2 log|Δ|)`. Set `C := C0 + 2 log|Δ|`, and prove
   `0 ≤ C` (C0 ≥ 0 from the raw seam — check its sign; if C0 can be negative, enlarge C to max(C,0)).

If a single genuinely-missing Mathlib lemma about `P1Q.logHeight` / `naiveLogHeightP1Q` / SameQ blocks
this, prove it as a local helper — do NOT leave it as a new axiom or a second sorry. The whole point is
to reach 0 sorries.

## RULES
- NO axiom-escape. Target = 0 sorries in scratch/A6TorsionFinite.lean.
- When done, run `grep -n "sorry\|admit\|axiom" scratch/A6TorsionFinite.lean` and
  `lake env lean scratch/A6TorsionFinite.lean`, PASTE BOTH VERBATIM, state the EXACT sorry count.
  Do NOT claim closure unless grep shows zero. (Prior passes misreported — be exact.)
- Unbounded grind. Only legitimate stop: math wrong, or a precisely-named missing Mathlib API that you
  cannot prove even as a local helper.
