# Q2403 (dm-codex1): E1 full-cover residual wrappers for AP covers

This drop gives a self-contained Lean block for the two AP residual covers and the corresponding `X`-forcing wrappers.

Paste inside, or adapt to, namespace `MazurProof.RationalPointsN12`.  If `CoverQ` and `FourRatSquaresAPConst` already exist in the file, omit the duplicate `def`s and keep the helper lemma plus four theorems.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Rational full-cover equations for fixed squareclass representatives. -/
def CoverQ (d0 d1 d3 : ℤ) (A B C T : ℚ) : Prop :=
  (d0 : ℚ)*A^2 - (d1 : ℚ)*B^2 = T^2 ∧
  (d3 : ℚ)*C^2 - (d0 : ℚ)*A^2 = (3:ℚ)*T^2

/-- Fermat four-rational-squares-in-arithmetic-progression theorem. -/
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
      w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2

/-- If `a^2=t^2` and `t≠0`, then `(a/t)^2=1`.  Kept separate so the
`X` wrappers avoid fragile large `field_simp` goals. -/
private lemma sq_div_eq_one_of_sq_eq {a t : ℚ}
    (ht : t ≠ 0) (h : a^2 = t^2) :
    (a / t)^2 = 1 := by
  have ht2 : t^2 ≠ 0 := pow_ne_zero 2 ht
  calc
    (a / t)^2 = a^2 / t^2 := by ring
    _ = t^2 / t^2 := by rw [h]
    _ = 1 := div_self ht2

/-- The `(3,2,6)` residual cover gives the AP
`B^2, A^2, C^2, T^2`, hence all four squares are equal. -/
theorem coverQ_3_2_6_AP_const
    (hAP : FourRatSquaresAPConst)
    {A B C T : ℚ}
    (h : CoverQ 3 2 6 A B C T) :
    T^2 = C^2 ∧ C^2 = A^2 ∧ A^2 = B^2 := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hap1 : A^2 - B^2 = C^2 - A^2 := by
    nlinarith [h1, h2]
  have hap2 : C^2 - A^2 = T^2 - C^2 := by
    nlinarith [h2]
  have hconst := hAP (w := B) (x := A) (y := C) (z := T) hap1 hap2
  rcases hconst with ⟨hBA, hAC, hCT⟩
  exact ⟨hCT.symm, hAC.symm, hBA.symm⟩

/-- The `(-1,-2,2)` residual cover gives the AP
`A^2, B^2, T^2, C^2`, hence all four squares are equal. -/
theorem coverQ_neg1_neg2_2_AP_const
    (hAP : FourRatSquaresAPConst)
    {A B C T : ℚ}
    (h : CoverQ (-1) (-2) 2 A B C T) :
    A^2 = B^2 ∧ B^2 = T^2 ∧ T^2 = C^2 := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hap1 : B^2 - A^2 = T^2 - B^2 := by
    nlinarith [h1]
  have hap2 : T^2 - B^2 = C^2 - T^2 := by
    nlinarith [h1, h2]
  exact hAP (w := A) (x := B) (y := T) (z := C) hap1 hap2

/-- On the `(3,2,6)` residual cover, the squareclass formula
`X = 3*(A/T)^2` forces `X = 3`. -/
theorem coverQ_3_2_6_forces_X_eq_three
    (hAP : FourRatSquaresAPConst)
    {A B C T X : ℚ}
    (hT : T ≠ 0)
    (hX : X = (3:ℚ) * (A / T)^2)
    (hcover : CoverQ 3 2 6 A B C T) :
    X = 3 := by
  have hconst := coverQ_3_2_6_AP_const hAP hcover
  rcases hconst with ⟨hTC, hCA, _hAB⟩
  have hAT : A^2 = T^2 := by
    nlinarith [hTC, hCA]
  have hratio : (A / T)^2 = 1 := sq_div_eq_one_of_sq_eq hT hAT
  rw [hratio] at hX
  norm_num at hX
  exact hX

/-- On the `(-1,-2,2)` residual cover, the squareclass formula
`X = -1*(A/T)^2` forces `X = -1`. -/
theorem coverQ_neg1_neg2_2_forces_X_eq_neg_one
    (hAP : FourRatSquaresAPConst)
    {A B C T X : ℚ}
    (hT : T ≠ 0)
    (hX : X = (-1:ℚ) * (A / T)^2)
    (hcover : CoverQ (-1) (-2) 2 A B C T) :
    X = -1 := by
  have hconst := coverQ_neg1_neg2_2_AP_const hAP hcover
  rcases hconst with ⟨hAB, hBT, _hTC⟩
  have hAT : A^2 = T^2 := by
    nlinarith [hAB, hBT]
  have hratio : (A / T)^2 = 1 := sq_div_eq_one_of_sq_eq hT hAT
  rw [hratio] at hX
  norm_num at hX
  exact hX

end MazurProof.RationalPointsN12
```

## Notes

The two AP conversions used above are exactly:

```text
(3,2,6):
  3A^2 - 2B^2 = T^2,
  6C^2 - 3A^2 = 3T^2
  -> A^2-B^2 = C^2-A^2
  -> C^2-A^2 = T^2-C^2.

(-1,-2,2):
  -A^2 + 2B^2 = T^2,
  2C^2 + A^2 = 3T^2
  -> B^2-A^2 = T^2-B^2
  -> T^2-B^2 = C^2-T^2.
```

The `X` wrappers only use `A^2=T^2` plus `T≠0`, via `sq_div_eq_one_of_sq_eq`; no extra cover algebra is repeated there.
