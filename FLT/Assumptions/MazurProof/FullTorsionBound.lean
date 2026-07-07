import FLT.Assumptions.MazurProof.NoFull3Torsion
import FLT.Assumptions.MazurProof.GroupTheory

/-!
# Full rational torsion bounds without the Weil-pairing interface

This file is the replacement landing point for uses of the old
`weil_interface_bridge` route.

The fully closed route is currently the real-topology bound:
`card_E_R_torsion_le` gives `m ^ 2 ≤ 2 * m`, hence full rational `m`-torsion
forces `m ≤ 2`.

The q-primary route is also recorded here in the form that is already useful
for reducing the remaining axiom load:

* `no_full_3_torsion` excludes full rational `m`-torsion whenever `3 ∣ m`.
* A future global no-full-4 theorem would similarly exclude all `4 ∣ m`.

These two exclusions alone do not imply `m ≤ 2`: orders such as `5`, `7`, `10`,
`11`, ... remain.  To close a purely elementary replacement for the
Weil-pairing route one still needs either all odd-prime square exclusions
together with the `4`-primary exclusion, or the Mazur cyclic order list plus
the additional exclusions for `q = 5` and `q = 7`.

As of this file, the final theorem `no_full_3_torsion` itself is imported as
an interface theorem.  The elementary quartic obstruction in
`NoFull3Torsion.lean` will become independent of real topology only after the
geometric bridge from full rational `3`-torsion to that quartic obstruction is
installed.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Closed route: real topology -/

/-- Full rational torsion has first invariant factor at most two, without using
the Weil-pairing interface. -/
theorem fullRationalTorsion_order_le_two_without_weil
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 :=
  fullRationalTorsion_order_le_two_route4B E hm hfull

/-! ## The `3`-primary exclusion -/

/-- The imported no-full-`3` theorem, in forward-implication form. -/
theorem full_rational_torsion_three_false
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hfull : HasFullRationalTorsion E 3) :
    False :=
  no_full_3_torsion E hfull

/-- If full rational `m`-torsion exists and `3 ∣ m`, then full rational
`3`-torsion exists. -/
theorem full_three_of_full_of_three_dvd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (h3m : 3 ∣ m)
    (hfull : HasFullRationalTorsion E m) :
    HasFullRationalTorsion E 3 := by
  obtain ⟨embed, hembed⟩ :=
    zmod_prod_contains_square_of_dvd 3 m m (by norm_num) hm hm h3m dvd_rfl
  obtain ⟨f, hf⟩ := hfull
  exact ⟨f.comp embed, hf.comp hembed⟩

/-- No full rational `m`-torsion can occur when `3 ∣ m`. -/
theorem no_full_rational_torsion_of_three_dvd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (h3m : 3 ∣ m) :
    ¬ HasFullRationalTorsion E m := by
  intro hfull
  exact no_full_3_torsion E (full_three_of_full_of_three_dvd E hm h3m hfull)

/-- In particular, full rational `9`-torsion is impossible. -/
theorem no_full_rational_torsion_nine
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasFullRationalTorsion E 9 :=
  no_full_rational_torsion_of_three_dvd E (m := 9) (by norm_num) (by norm_num)

/-- Full rational `m`-torsion forces `3 ∤ m`. -/
theorem three_not_dvd_of_full_rational_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ¬ 3 ∣ m := by
  intro h3m
  exact no_full_rational_torsion_of_three_dvd E hm h3m hfull

/-! ## First invariant factor version -/

/-- If a torsion structure has first invariant factor divisible by `3`, it
would contain full rational `3`-torsion. -/
theorem full_three_of_torsion_structure_of_three_dvd_first_factor
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) (h3m : 3 ∣ m)
    (hstruct : HasTorsionStructure E m n) :
    HasFullRationalTorsion E 3 := by
  obtain ⟨embed, hembed⟩ :=
    zmod_prod_contains_square_of_dvd 3 m n (by norm_num) hm hn h3m hmn
  obtain ⟨f, hf⟩ := hstruct
  exact ⟨f.comp embed, hf.comp hembed⟩

/-- Hence the first invariant factor in a rational torsion structure is not
divisible by `3`. -/
theorem three_not_dvd_first_factor_of_torsion_structure
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (hstruct : HasTorsionStructure E m n) :
    ¬ 3 ∣ m := by
  intro h3m
  exact no_full_3_torsion E
    (full_three_of_torsion_structure_of_three_dvd_first_factor
      E hm hn hmn h3m hstruct)

/-! ## Conditional `4`-primary analogues

`NoFull4Torsion.lean` currently proves the elementary halving obstruction but
still has the classical halving criterion as a remaining theorem-level seam.
Once that file exports `¬ HasFullRationalTorsion E 4`, the following wiring
excludes every first invariant factor divisible by `4`.
-/

/-- Conditional `4`-primary analogue of `full_three_of_full_of_three_dvd`. -/
theorem full_four_of_full_of_four_dvd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (h4m : 4 ∣ m)
    (hfull : HasFullRationalTorsion E m) :
    HasFullRationalTorsion E 4 := by
  obtain ⟨embed, hembed⟩ :=
    zmod_prod_contains_square_of_dvd 4 m m (by norm_num) hm hm h4m dvd_rfl
  obtain ⟨f, hf⟩ := hfull
  exact ⟨f.comp embed, hf.comp hembed⟩

/-- If no elliptic curve has full rational `4`-torsion, then full rational
`m`-torsion is impossible for every `m` divisible by `4`. -/
theorem no_full_rational_torsion_of_four_dvd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (h4 : ¬ HasFullRationalTorsion E 4)
    (hm : 0 < m) (h4m : 4 ∣ m) :
    ¬ HasFullRationalTorsion E m := by
  intro hfull
  exact h4 (full_four_of_full_of_four_dvd E hm h4m hfull)

/-- Conditional first-invariant-factor version of the `4`-primary exclusion. -/
theorem four_not_dvd_first_factor_of_torsion_structure
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m n : ℕ}
    (h4 : ¬ HasFullRationalTorsion E 4)
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (hstruct : HasTorsionStructure E m n) :
    ¬ 4 ∣ m := by
  intro h4m
  obtain ⟨embed, hembed⟩ :=
    zmod_prod_contains_square_of_dvd 4 m n (by norm_num) hm hn h4m hmn
  obtain ⟨f, hf⟩ := hstruct
  exact h4 ⟨f.comp embed, hf.comp hembed⟩

end MazurProof
