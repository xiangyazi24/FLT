# Q44 (dm3): Keystone avenue (c) capstone assembly

This is the capstone I would drop in after the rank-3/resultant lemmas are
finalized.  It assumes the helper theorem names from the prompt are present in
`namespace WeierstrassCurve`:

```lean
no_adjacent_preΨ_zero_of_Ψ₃_eval_ne
no_adjacent_preΨ_zero_of_Ψ₃_eval_zero
Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero
Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero
preΨ₄_eval_ne_of_Ψ₃_eval_zero
```

The consumer lemma in `KeystoneSameP1.lean` must gain `[W.IsElliptic]`; without
that hypothesis the infinity-branch no-common-root assertion is false on singular
curves.

---

## 1. `scratch/KeystoneCoprimality.lean`

Put this in `namespace WeierstrassCurve`, after the two adjacent-zero lemmas and
the resultant/nonsingularity certificates.

```lean
namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k]

/--
Avenue (c) capstone: no two adjacent `preΨ` values vanish at an elliptic
specialization.

If `Ψ₃(x) ≠ 0`, use the already-proved generic adjacent-zero lemma.  If
`Ψ₃(x) = 0`, the resultant certificates supply the two nonzero inputs needed by
the rank-3 apparition lemma.
-/
theorem no_adjacent_preΨ_zero
    (W : WeierstrassCurve k) [W.IsElliptic] (x : k)
    (h4 : (4 : k) ≠ 0) (r : ℤ) :
    ¬ (pe W x r = 0 ∧ pe W x (r + 1) = 0) := by
  by_cases hc3 : c3x W x = 0
  · have hs2 : sx W x ≠ 0 :=
      Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero (W := W) (x := x) hc3
    have hd4 : (W.preΨ 4).eval x ≠ 0 :=
      preΨ₄_eval_ne_of_Ψ₃_eval_zero (W := W) (x := x) hc3
    exact no_adjacent_preΨ_zero_of_Ψ₃_eval_zero
      (W := W) (x := x) h4 hs2 hd4 hc3 r
  · exact no_adjacent_preΨ_zero_of_Ψ₃_eval_ne
      (W := W) (x := x) h4 hc3 r

/-- Odd `ΨSq` evaluation: at odd index it is just `preΨ²`. -/
theorem ΨSq_eval_odd
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    (W.ΨSq (2 * m + 1)).eval x = (pe W x (2 * m + 1)) ^ 2 := by
  simp [ΨSq, pe, m.not_even_two_mul_add_one]

/-- Odd `Φ` evaluation in the `pe/sx` notation used by the coprimality file. -/
theorem Φ_eval_odd
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    (W.Φ (2 * m + 1)).eval x
      = x * (W.ΨSq (2 * m + 1)).eval x
          - pe W x ((2 * m + 1) + 1) * pe W x ((2 * m + 1) - 1) * sx W x := by
  simp [WeierstrassCurve.Φ, pe, sx, m.not_even_two_mul_add_one]
  ring

/--
At a nonsingular 2-torsion specialization (`Ψ₂Sq(x)=0`), no odd `preΨ_n(x)`
vanishes.

The proof is the promised strong induction on positive odd indices.  It uses
Mathlib's `normEDSRec'` recursion principle for the natural-indexed EDS.  In the
odd recursive branch, the recurrence

```lean
W.preΨ'_odd m
```

collapses after evaluation at `x` because `(W.Ψ₂Sq).eval x = 0`.

* if `Even m`, then
  `preΨ' (2*(m+2)+1) = - preΨ'(m+1) * preΨ'(m+3)^3`;
* if `¬ Even m`, then
  `preΨ' (2*(m+2)+1) = preΨ'(m+4) * preΨ'(m+2)^3`.

The bases are `preΨ_1 = 1` and `preΨ_3 = Ψ₃`, with the latter nonzero by the
resultant certificate `Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero`.
-/
theorem preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero
    (W : WeierstrassCurve k) [W.IsElliptic] (x : k)
    (h4 : (4 : k) ≠ 0) (hs : sx W x = 0)
    {n : ℤ} (hn : ¬ Even n) :
    pe W x n ≠ 0 := by
  classical

  have hc3_ne : c3x W x ≠ 0 :=
    Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero (W := W) (x := x) hs

  have hNat : ∀ N : ℕ, ¬ Even ((N : ℕ) : ℤ) → pe W x ((N : ℕ) : ℤ) ≠ 0 := by
    intro N
    induction N using normEDSRec' with
    | zero =>
        intro hodd
        exact False.elim <| hodd (by decide)
    | one =>
        intro _
        simp [pe]
    | two =>
        intro hodd
        exact False.elim <| hodd (by decide)
    | three =>
        intro _
        simpa [pe, c3x] using hc3_ne
    | four =>
        intro hodd
        exact False.elim <| hodd (by decide)
    | even m ih =>
        intro hodd
        exfalso
        apply hodd
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          (even_two_mul (((m + 3 : ℕ) : ℤ)))
    | odd m ih =>
        intro _hodd_target
        by_cases hm : Even m
        · have hrec :
              pe W x (((2 * (m + 2) + 1 : ℕ) : ℤ))
                = - (pe W x (((m + 1 : ℕ) : ℤ)) *
                      pe W x (((m + 3 : ℕ) : ℤ)) ^ 3) := by
            have h := congrArg (fun p : Polynomial k => p.eval x) (W.preΨ'_odd m)
            simpa [pe, sx, hs, hm] using h

          have hm1_odd : ¬ Even (((m + 1 : ℕ) : ℤ)) := by
            intro hbad
            rcases hm with ⟨a, ha⟩
            rcases hbad with ⟨b, hb⟩
            omega
          have hm3_odd : ¬ Even (((m + 3 : ℕ) : ℤ)) := by
            intro hbad
            rcases hm with ⟨a, ha⟩
            rcases hbad with ⟨b, hb⟩
            omega

          have hm1_ne : pe W x (((m + 1 : ℕ) : ℤ)) ≠ 0 :=
            ih (m + 1) (by omega) hm1_odd
          have hm3_ne : pe W x (((m + 3 : ℕ) : ℤ)) ≠ 0 :=
            ih (m + 3) (by omega) hm3_odd

          rw [hrec]
          exact neg_ne_zero.mpr <| mul_ne_zero hm1_ne (pow_ne_zero 3 hm3_ne)

        · have hm_pos : 0 < m := by
            by_contra hpos
            have hm0 : m = 0 := Nat.eq_zero_of_not_pos hpos
            subst m
            exact hm (by decide)

          have hrec :
              pe W x (((2 * (m + 2) + 1 : ℕ) : ℤ))
                = pe W x (((m + 4 : ℕ) : ℤ)) *
                    pe W x (((m + 2 : ℕ) : ℤ)) ^ 3 := by
            have h := congrArg (fun p : Polynomial k => p.eval x) (W.preΨ'_odd m)
            simpa [pe, sx, hs, hm] using h

          have hm2_odd : ¬ Even (((m + 2 : ℕ) : ℤ)) := by
            intro hbad
            apply hm
            have hm_even_z : Even ((m : ℕ) : ℤ) := by
              rcases hbad with ⟨a, ha⟩
              refine ⟨a - 1, ?_⟩
              omega
            exact Int.even_coe_nat.mp hm_even_z
          have hm4_odd : ¬ Even (((m + 4 : ℕ) : ℤ)) := by
            intro hbad
            apply hm
            have hm_even_z : Even ((m : ℕ) : ℤ) := by
              rcases hbad with ⟨a, ha⟩
              refine ⟨a - 2, ?_⟩
              omega
            exact Int.even_coe_nat.mp hm_even_z

          have hm2_ne : pe W x (((m + 2 : ℕ) : ℤ)) ≠ 0 :=
            ih (m + 2) (by omega) hm2_odd
          have hm4_ne : pe W x (((m + 4 : ℕ) : ℤ)) ≠ 0 :=
            ih (m + 4) (by omega) hm4_odd

          rw [hrec]
          exact mul_ne_zero hm4_ne (pow_ne_zero 3 hm2_ne)

  rcases lt_trichotomy n 0 with hn_neg | hn_zero | hn_pos
  · let N : ℕ := Int.toNat (-n)
    have hNcast : ((N : ℕ) : ℤ) = -n := by
      dsimp [N]
      exact Int.toNat_of_nonneg (by omega)
    have hneg_odd : ¬ Even (-n) := by
      intro h
      exact hn (by simpa [even_neg] using h)
    have hNodd : ¬ Even ((N : ℕ) : ℤ) := by
      simpa [hNcast] using hneg_odd
    have hne_neg : pe W x (-n) ≠ 0 := by
      simpa [hNcast] using hNat N hNodd
    intro hn_zero_eval
    apply hne_neg
    have hpre_neg : pe W x (-n) = - pe W x n := by
      simpa [pe] using congrArg (fun p : Polynomial k => p.eval x) (W.preΨ_neg n)
    simp [hpre_neg, hn_zero_eval]
  · subst n
    exact False.elim <| hn (by decide)
  · let N : ℕ := Int.toNat n
    have hNcast : ((N : ℕ) : ℤ) = n := by
      dsimp [N]
      exact Int.toNat_of_nonneg (by omega)
    have hNodd : ¬ Even ((N : ℕ) : ℤ) := by
      simpa [hNcast] using hn
    simpa [hNcast] using hNat N hNodd

/--
Odd `Φ` and `ΨSq` have no common evaluated zero on an elliptic curve.

This is the avenue (c) no-common-root theorem needed by the x-only ladder
infinity branch.
-/
theorem Φ_ΨSq_no_common_eval_zero_odd
    (W : WeierstrassCurve k) [W.IsElliptic] (x : k)
    (h4 : (4 : k) ≠ 0) (m : ℤ) :
    ¬ ((W.Φ (2 * m + 1)).eval x = 0 ∧
        (W.ΨSq (2 * m + 1)).eval x = 0) := by
  rintro ⟨hΦ, hΨ⟩

  have hpe_sq : (pe W x (2 * m + 1)) ^ 2 = 0 := by
    simpa [ΨSq_eval_odd (W := W) (x := x) (m := m)] using hΨ
  have hpe : pe W x (2 * m + 1) = 0 := sq_eq_zero_iff.mp hpe_sq

  by_cases hs : sx W x = 0
  · exact (preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero
      (W := W) (x := x) h4 hs (n := 2 * m + 1)
      m.not_even_two_mul_add_one) hpe

  · have hΦformula := Φ_eval_odd (W := W) (x := x) (m := m)

    have hprod_sx :
        pe W x ((2 * m + 1) + 1) * pe W x ((2 * m + 1) - 1) * sx W x = 0 := by
      have hzero :
          (0 : k)
            = - (pe W x ((2 * m + 1) + 1) *
                  pe W x ((2 * m + 1) - 1) * sx W x) := by
        simpa [hΦ, hΨ] using hΦformula
      exact neg_eq_zero.mp hzero.symm

    have hprod :
        pe W x ((2 * m + 1) + 1) * pe W x ((2 * m + 1) - 1) = 0 :=
      (mul_eq_zero.mp hprod_sx).resolve_right hs

    rcases mul_eq_zero.mp hprod with hnext | hprev
    · have hnext' : pe W x (2 * m + 2) = 0 := by
        simpa only [show (2 * m + 1) + 1 = 2 * m + 2 by ring] using hnext
      exact (no_adjacent_preΨ_zero (W := W) (x := x) h4 (2 * m + 1))
        ⟨hpe, by simpa only [show (2 * m + 1) + 1 = 2 * m + 2 by ring] using hnext'⟩
    · have hprev' : pe W x (2 * m) = 0 := by
        simpa only [show (2 * m + 1) - 1 = 2 * m by ring] using hprev
      exact (no_adjacent_preΨ_zero (W := W) (x := x) h4 (2 * m))
        ⟨hprev', by simpa only [show 2 * m + 1 = 2 * m + 1 by ring] using hpe⟩

end WeierstrassCurve
```

### Notes on likely local-name adjustments

If your finalized certificate lemmas include `h4` as an explicit argument, change
only the three certificate calls, for example:

```lean
Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero (W := W) (x := x) h4 hc3
Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero (W := W) (x := x) h4 hs
preΨ₄_eval_ne_of_Ψ₃_eval_zero (W := W) (x := x) h4 hc3
```

The core proof shape should not change.

---

## 2. `scratch/KeystoneSameP1.lean` consumer hookup

The earlier wiring lemma had the right branch split, but its infinity branch
needed the `Φ/ΨSq` no-common-root fact.  Therefore the consumer lemma and final
`xPair_diffAdd_sameP1` theorem must gain `[W.IsElliptic]`.

Put this in `namespace KeystoneLadder.XOnly`, replacing the old sorry/placeholder
lemma.

```lean
namespace KeystoneLadder
namespace XOnly

open Polynomial

variable {k : Type*} [Field k]

/--
Infinity-branch nonzero scalar for odd diff-add.

Corrected signature: this genuinely needs `[W.IsElliptic]`.  The hypotheses
`hψ_ne` and `hc3` are still kept because the wiring file obtains
`ΨSq(2*m+1)` from the already-proved diff-add denominator identity, which has the
same assumptions as the projective diff-add certificate.
-/
theorem xPair_odd_phi_eval_ne_zero_of_delta_zero
    (W : WeierstrassCurve k) [W.IsElliptic]
    (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0) (hψ_ne) (hc3)
    (hδ : deltaVec (xPair W (m + 1) x) (xPair W m x) = 0) :
    (W.Φ (2 * m + 1)).eval x ≠ 0 := by
  have hΨzero : (W.ΨSq (2 * m + 1)).eval x = 0 := by
    calc
      (W.ΨSq (2 * m + 1)).eval x
          = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
              exact ΨSq_two_mul_add_one_eval_deltaVec_sq
                (W := W) (m := m) (x := x) h4 hψ_ne hc3
      _ = 0 := by simp [hδ]

  intro hΦzero
  exact (WeierstrassCurve.Φ_ΨSq_no_common_eval_zero_odd
    (W := W) (x := x) h4 m) ⟨hΦzero, hΨzero⟩

/-- Keystone x-only differential-addition wiring lemma, corrected with ellipticity. -/
theorem xPair_diffAdd_sameP1
    (W : WeierstrassCurve k) [W.IsElliptic]
    (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0) (hψ_ne) (hc3) :
    SameP1Vec
      (diffAddOrInfVec (E := W⁄k)
        (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x))
      (xPair W (2 * m + 1) x) := by
  refine xPair_diffAdd_sameP1_of_inf_phi_ne
    (W := W) (m := m) (x := x) h4 hψ_ne hc3 ?_
  intro hδ
  exact xPair_odd_phi_eval_ne_zero_of_delta_zero
    (W := W) (m := m) (x := x) h4 hψ_ne hc3 hδ

end XOnly
end KeystoneLadder
```

If `xPair_diffAdd_sameP1_of_inf_phi_ne` was kept as the isolated wiring theorem
from the previous drop, no change is needed to it: it remains pure wiring and does
not require ellipticity.  The ellipticity enters exactly at the `hΦinf` supplier
above.
