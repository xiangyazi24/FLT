```lean
theorem intFourSqAP_left_three {w x y z : Int} (hAP : IntFourSqAP w x y z) :
    w ^ 2 + y ^ 2 = 2 * x ^ 2 := by
  cases hAP with
  | intro hleft hright =>
      nlinarith

theorem intFourSqAP_right_three {w x y z : Int} (hAP : IntFourSqAP w x y z) :
    x ^ 2 + z ^ 2 = 2 * y ^ 2 := by
  cases hAP with
  | intro hleft hright =>
      nlinarith

theorem intFourSqAP_outer_sum {w x y z : Int} (hAP : IntFourSqAP w x y z) :
    w ^ 2 + z ^ 2 = x ^ 2 + y ^ 2 := by
  cases hAP with
  | intro hleft hright =>
      nlinarith

theorem intFourSqAP_outer_diff {w x y z : Int} (hAP : IntFourSqAP w x y z) :
    z ^ 2 - w ^ 2 = 3 * (y ^ 2 - x ^ 2) := by
  cases hAP with
  | intro hleft hright =>
      nlinarith

theorem fourSqAPConst_of_intFourSqAP_commonDiff_zero {w x y z : Int}
    (hAP : IntFourSqAP w x y z) (hzero : y ^ 2 - x ^ 2 = 0) :
    FourSqAPConst w x y z := by
  cases hAP with
  | intro hleft hright =>
      unfold FourSqAPConst
      refine And.intro ?_ (And.intro ?_ ?_)
      · nlinarith
      · nlinarith
      · nlinarith

theorem intFourSqAP_commonDiff_ne_zero_of_nonconst {w x y z : Int}
    (hAP : IntFourSqAP w x y z) (hnonconst : Not (FourSqAPConst w x y z)) :
    Not (y ^ 2 - x ^ 2 = 0) := by
  intro hzero
  exact hnonconst
    (fourSqAPConst_of_intFourSqAP_commonDiff_zero
      (w := w) (x := x) (y := y) (z := z) hAP hzero)

theorem intFourSqAP_factor_xy_wz {w x y z : Int} (hAP : IntFourSqAP w x y z) :
    (x * y - w * z) * (x * y + w * z) =
      2 * (y ^ 2 - x ^ 2) ^ 2 := by
  have hw : w ^ 2 = 2 * x ^ 2 - y ^ 2 := by
    nlinarith [intFourSqAP_left_three hAP]
  have hz : z ^ 2 = 2 * y ^ 2 - x ^ 2 := by
    nlinarith [intFourSqAP_right_three hAP]
  calc
    (x * y - w * z) * (x * y + w * z)
        = x ^ 2 * y ^ 2 - w ^ 2 * z ^ 2 := by
          ring
    _ = x ^ 2 * y ^ 2 - (2 * x ^ 2 - y ^ 2) * (2 * y ^ 2 - x ^ 2) := by
          rw [hw, hz]
    _ = 2 * (y ^ 2 - x ^ 2) ^ 2 := by
          ring

theorem intFourSqAP_factor_xz_wy {w x y z : Int} (hAP : IntFourSqAP w x y z) :
    (x * z - w * y) * (x * z + w * y) =
      (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by
  have hw : w ^ 2 = 2 * x ^ 2 - y ^ 2 := by
    nlinarith [intFourSqAP_left_three hAP]
  have hz : z ^ 2 = 2 * y ^ 2 - x ^ 2 := by
    nlinarith [intFourSqAP_right_three hAP]
  calc
    (x * z - w * y) * (x * z + w * y)
        = x ^ 2 * z ^ 2 - w ^ 2 * y ^ 2 := by
          ring
    _ = x ^ 2 * (2 * y ^ 2 - x ^ 2) - (2 * x ^ 2 - y ^ 2) * y ^ 2 := by
          rw [hw, hz]
    _ = (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by
          ring

theorem intFourSqAP_factor_yz_wx {w x y z : Int} (hAP : IntFourSqAP w x y z) :
    (y * z - w * x) * (y * z + w * x) =
      2 * (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by
  have hw : w ^ 2 = 2 * x ^ 2 - y ^ 2 := by
    nlinarith [intFourSqAP_left_three hAP]
  have hz : z ^ 2 = 2 * y ^ 2 - x ^ 2 := by
    nlinarith [intFourSqAP_right_three hAP]
  calc
    (y * z - w * x) * (y * z + w * x)
        = y ^ 2 * z ^ 2 - w ^ 2 * x ^ 2 := by
          ring
    _ = y ^ 2 * (2 * y ^ 2 - x ^ 2) - (2 * x ^ 2 - y ^ 2) * x ^ 2 := by
          rw [hw, hz]
    _ = 2 * (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by
          ring
```