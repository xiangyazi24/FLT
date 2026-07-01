# Q2956 (dm-codex1): robust Lean snippets for `KParamScratch`

Paste this into `scratch/KParamScratch.lean` after your scratch definitions.  The key trick in the two recovery lemmas is: set

```lean
A = 2 * r ^ 2 + r - c
D = c - r
```

then prove `A / D + 1 ≠ 0` before `field_simp`.  This prevents `field_simp` from normalizing through `q + 1 = 2*r^2/D` in a way that leaves `r⁻¹` powers.

```lean
import FLT.Assumptions.MazurProof.KubertBridgeN12
import Mathlib.Tactic

namespace MazurProof.KubertBridgeN12

noncomputable section

private def tateC12_rInv_scratch (b c : ℚ) : ℚ :=
  (b - c) / c

private def tateC12_qInv_scratch (b c : ℚ) : ℚ :=
  -1 - 2 * (b - c) ^ 2 / (c * (b - c - c ^ 2))

private lemma tateC12_qInv_rform_scratch
    (b c : ℚ) (hc : c ≠ 0) (h6 : b - c - c ^ 2 ≠ 0) :
    let r : ℚ := tateC12_rInv_scratch b c
    tateC12_qInv_scratch b c = (2 * r ^ 2 + r - c) / (c - r) := by
  dsimp [tateC12_qInv_scratch, tateC12_rInv_scratch]
  have h6neg : -(b - c - c ^ 2) ≠ 0 := by
    exact neg_ne_zero.mpr h6
  have h6comm : -c - c ^ 2 + b ≠ 0 := by
    intro h
    apply h6
    linarith
  have h6alt : b - c ^ 2 - c ≠ 0 := by
    intro h
    apply h6
    linarith
  have hden : c * (b - c - c ^ 2) ≠ 0 := by
    exact mul_ne_zero hc h6
  have hden_comm : c * (-c - c ^ 2 + b) ≠ 0 := by
    exact mul_ne_zero hc h6comm
  have hden_alt : c * (b - c ^ 2 - c) ≠ 0 := by
    exact mul_ne_zero hc h6alt
  have hcr_eq :
      c - (b - c) / c = -(b - c - c ^ 2) / c := by
    field_simp [hc]
    ring
  have hcr_div : -(b - c - c ^ 2) / c ≠ 0 := by
    exact div_ne_zero h6neg hc
  rw [hcr_eq]
  field_simp [hc, h6, h6neg, h6comm, h6alt,
    hden, hden_comm, hden_alt, hcr_div]
  ring

private lemma tateC12_qInv_recovers_r_scratch
    {r c : ℚ}
    (hF : c ^ 2 - c * r * (r ^ 2 + 3 * r + 2) +
      r ^ 2 * (3 * r ^ 2 + 3 * r + 1) = 0)
    (hr : r ≠ 0) (hcr : c - r ≠ 0) :
    let q : ℚ := (2 * r ^ 2 + r - c) / (c - r)
    q * (q - 1) / (q + 1) = r := by
  dsimp
  set A : ℚ := 2 * r ^ 2 + r - c with hA
  set D : ℚ := c - r with hDdef
  have hDnz : D ≠ 0 := by
    simpa [hDdef] using hcr
  have hq1 : A / D + 1 ≠ 0 := by
    have hq1_eq : A / D + 1 = (2 * r ^ 2) / D := by
      field_simp [hDnz, hA, hDdef]
      ring
    rw [hq1_eq]
    exact div_ne_zero
      (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) (pow_ne_zero 2 hr))
      hDnz
  field_simp [hDnz, hq1]
  subst A
  subst D
  ring_nf at hF ⊢
  nlinarith

private lemma tateC12_qInv_recovers_c_scratch
    {r c : ℚ}
    (hF : c ^ 2 - c * r * (r ^ 2 + 3 * r + 2) +
      r ^ 2 * (3 * r ^ 2 + 3 * r + 1) = 0)
    (hr : r ≠ 0) (hcr : c - r ≠ 0) :
    let q : ℚ := (2 * r ^ 2 + r - c) / (c - r)
    r * (3 * q ^ 2 + 1) / (q + 1) ^ 2 = c := by
  dsimp
  set A : ℚ := 2 * r ^ 2 + r - c with hA
  set D : ℚ := c - r with hDdef
  have hDnz : D ≠ 0 := by
    simpa [hDdef] using hcr
  have hq1 : A / D + 1 ≠ 0 := by
    have hq1_eq : A / D + 1 = (2 * r ^ 2) / D := by
      field_simp [hDnz, hA, hDdef]
      ring
    rw [hq1_eq]
    exact div_ne_zero
      (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) (pow_ne_zero 2 hr))
      hDnz
  field_simp [hDnz, hq1]
  subst A
  subst D
  ring_nf at hF ⊢
  nlinarith

end

end MazurProof.KubertBridgeN12
```

If your local file already imports `Mathlib.Tactic` indirectly, the second import is harmless.  If the scratch definitions already exist, delete the duplicate `private def` lines above and keep only the three lemmas.
