module

public import scratch.KeystoneSameP1

/-! # Keystone avenue (d): EDS core + export chain, relocated above SameP1 + Coprimality.
The L1009 core is proven here (non-circular) and the downstream ladder/export is threaded
with (h4, hψ_ne, hc3). KeystoneLadder.lean truncated at L993. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {k : Type*} [Field k]

namespace KeystoneLadder
open XOnly

private lemma xPair_ne_zero_of_Φ_ΨSq_no_common
    (W : WeierstrassCurve k) (n : ℤ) (x : k)
    (h : ¬ ((W.Φ n).eval x = 0 ∧
            (W.ΨSq n).eval x = 0)) :
    xPair W n x ≠ 0 := by
  intro hv
  apply h
  constructor
  · have h0 := congrFun hv (0 : Fin 2)
    simpa [xPair] using h0
  · have h1 := congrFun hv (1 : Fin 2)
    simpa [xPair] using h1

private theorem xPair_double_and_diffAddOrInf_EDS_core
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    xPair W ((2 * m : ℕ) : ℤ) x ≠ 0 ∧
    SameP1Vec
      (XOnly.doubleVec (E := W⁄k) (xPair W (m : ℤ) x))
      (xPair W ((2 * m : ℕ) : ℤ) x) ∧
    xPair W ((2 * m + 1 : ℕ) : ℤ) x ≠ 0 ∧
    SameP1Vec
      (XOnly.diffAddOrInfVec (E := W⁄k)
        (xPair W (m : ℤ) x)
        (xPair W ((m + 1 : ℕ) : ℤ) x)
        (xPair W (1 : ℤ) x))
      (xPair W ((2 * m + 1 : ℕ) : ℤ) x) := by
  have h2m_no_common :
      ¬ ((W.Φ (2 * (m : ℤ))).eval x = 0 ∧
         (W.ΨSq (2 * (m : ℤ))).eval x = 0) := by
    simpa using
      (Φ_ΨSq_no_common_eval_zero_even
        (W := W) (x := x) (h4 := h4) (m := (m : ℤ)))

  have h2m_ne : xPair W ((2 * m : ℕ) : ℤ) x ≠ 0 := by
    refine xPair_ne_zero_of_Φ_ΨSq_no_common
      (W := W) (n := ((2 * m : ℕ) : ℤ)) (x := x) ?_
    simpa using h2m_no_common

  have h2m1_no_common :
      ¬ ((W.Φ (2 * (m : ℤ) + 1)).eval x = 0 ∧
         (W.ΨSq (2 * (m : ℤ) + 1)).eval x = 0) := by
    simpa using
      (Φ_ΨSq_no_common_eval_zero_odd
        (W := W) (x := x) (h4 := h4) (m := (m : ℤ)))

  have h2m1_ne : xPair W ((2 * m + 1 : ℕ) : ℤ) x ≠ 0 := by
    refine xPair_ne_zero_of_Φ_ΨSq_no_common
      (W := W) (n := ((2 * m + 1 : ℕ) : ℤ)) (x := x) ?_
    simpa using h2m1_no_common

  have hdouble_int :
      SameP1Vec
        (XOnly.doubleVec (E := W⁄k) (xPair W (m : ℤ) x))
        (xPair W (2 * (m : ℤ)) x) := by
    exact
      xPair_double_sameP1
        (W := W) (m := (m : ℤ)) (x := x)
        h4 hψ_ne hc3

  have hdouble :
      SameP1Vec
        (XOnly.doubleVec (E := W⁄k) (xPair W (m : ℤ) x))
        (xPair W ((2 * m : ℕ) : ℤ) x) := by
    simpa using hdouble_int

  have hdiff_int :
      SameP1Vec
        (XOnly.diffAddOrInfVec (E := W⁄k)
          (xPair W (m : ℤ) x)
          (xPair W ((m : ℤ) + 1) x)
          (xPair W (1 : ℤ) x))
        (xPair W (2 * (m : ℤ) + 1) x) := by
    exact
      xPair_diffAdd_sameP1_core_order
        (W := W) (m := (m : ℤ)) (x := x)
        h4 hψ_ne hc3

  have hdiff :
      SameP1Vec
        (XOnly.diffAddOrInfVec (E := W⁄k)
          (xPair W (m : ℤ) x)
          (xPair W ((m + 1 : ℕ) : ℤ) x)
          (xPair W (1 : ℤ) x))
        (xPair W ((2 * m + 1 : ℕ) : ℤ) x) := by
    simpa using hdiff_int

  exact ⟨h2m_ne, hdouble, h2m1_ne, hdiff⟩

private theorem xLadderPair_same_xPair_EDS
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    xPair W (n : ℤ) x ≠ 0 ∧
    xPair W ((n + 1 : ℕ) : ℤ) x ≠ 0 ∧
    SameP1Vec
      (XOnly.xLadderPair (E := W⁄k) x n).1
      (xPair W (n : ℤ) x) ∧
    SameP1Vec
      (XOnly.xLadderPair (E := W⁄k) x n).2
      (xPair W ((n + 1 : ℕ) : ℤ) x) := by
    classical
    have hD :
        SameP1Vec (XOnly.xAffVec x) (xPair W (1 : ℤ) x) := by
      simpa [xPair, XOnly.xAffVec] using SameP1Vec.refl (![x, 1] : Fin 2 → k)
    induction n using Nat.strong_induction_on with
    | h n IH =>
        rcases n with _ | n
        · constructor
          · simp [xPair]
          · constructor
            · simp [xPair]
            · constructor
              · simpa [XOnly.xLadderPair, xPair, XOnly.xInfVec] using
                  SameP1Vec.refl (![1, 0] : Fin 2 → k)
              · simpa [XOnly.xLadderPair] using hD
        · rcases n with _ | n
          · have hcore := xPair_double_and_diffAddOrInf_EDS_core (W := W) 1 x h4 hψ_ne hc3
            have hdouble :
                SameP1Vec
                  (XOnly.doubleVec (E := W⁄k) (XOnly.xAffVec x))
                  (xPair W (2 : ℤ) x) := by
              exact SameP1Vec.trans (XOnly.doubleVec_congr (E := W⁄k) hD) hcore.2.1
            constructor
            · simp [xPair]
            · constructor
              · simpa using hcore.1
              · constructor
                · simpa [XOnly.xLadderPair] using hD
                · simpa [XOnly.xLadderPair] using hdouble
          · let N : ℕ := n + 2
            let m : ℕ := N / 2
            change
              xPair W (N : ℤ) x ≠ 0 ∧
              xPair W ((N + 1 : ℕ) : ℤ) x ≠ 0 ∧
              SameP1Vec
                (XOnly.xLadderPair (E := W⁄k) x N).1
                (xPair W (N : ℤ) x) ∧
              SameP1Vec
                (XOnly.xLadderPair (E := W⁄k) x N).2
                (xPair W ((N + 1 : ℕ) : ℤ) x)
            have hm_lt : m < N := by
              dsimp [m, N]
              omega
            have IHm := IH m (by
              dsimp [m, N]
              omega)
            have hcore_m := xPair_double_and_diffAddOrInf_EDS_core (W := W) m x h4 hψ_ne hc3
            have hcore_ms := xPair_double_and_diffAddOrInf_EDS_core (W := W) (m + 1) x h4 hψ_ne hc3
            have hdouble₀ :
                SameP1Vec
                  (XOnly.doubleVec (E := W⁄k) (XOnly.xLadderPair (E := W⁄k) x m).1)
                  (xPair W ((2 * m : ℕ) : ℤ) x) := by
              exact SameP1Vec.trans
                (XOnly.doubleVec_congr (E := W⁄k) IHm.2.2.1)
                hcore_m.2.1
            have hadd :
                SameP1Vec
                  (XOnly.diffAddOrInfVec (E := W⁄k)
                    (XOnly.xLadderPair (E := W⁄k) x m).1
                    (XOnly.xLadderPair (E := W⁄k) x m).2
                    (XOnly.xAffVec x))
                  (xPair W ((2 * m + 1 : ℕ) : ℤ) x) := by
              exact SameP1Vec.trans
                (XOnly.diffAddOrInfVec_congr (E := W⁄k) IHm.2.2.1 IHm.2.2.2 hD)
                hcore_m.2.2.2
            have hdouble₁ :
                SameP1Vec
                  (XOnly.doubleVec (E := W⁄k) (XOnly.xLadderPair (E := W⁄k) x m).2)
                  (xPair W ((2 * (m + 1) : ℕ) : ℤ) x) := by
              exact SameP1Vec.trans
                (XOnly.doubleVec_congr (E := W⁄k) IHm.2.2.2)
                hcore_ms.2.1
            by_cases hEven : Even N
            · have hN : N = 2 * m := by
                simpa [m] using (Nat.two_mul_div_two_of_even hEven).symm
              have hN1 : N + 1 = 2 * m + 1 := by omega
              constructor
              · simpa [hN] using hcore_m.1
              · constructor
                · simpa [hN1] using hcore_m.2.2.1
                · constructor
                  · have hfirst :
                      SameP1Vec
                        (XOnly.doubleVec (E := W⁄k)
                          (XOnly.xLadderPair (E := W⁄k) x m).1)
                        (xPair W (N : ℤ) x) := by
                      simpa [hN] using hdouble₀
                    simpa [XOnly.xLadderPair, N, m, hEven] using hfirst
                  · have hsecond :
                      SameP1Vec
                        (XOnly.diffAddOrInfVec (E := W⁄k)
                          (XOnly.xLadderPair (E := W⁄k) x m).1
                          (XOnly.xLadderPair (E := W⁄k) x m).2
                          (XOnly.xAffVec x))
                        (xPair W ((N + 1 : ℕ) : ℤ) x) := by
                      simpa [hN1] using hadd
                    simpa [XOnly.xLadderPair, N, m, hEven] using hsecond
            · have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
              have hN : N = 2 * m + 1 := by
                simpa [m] using (Nat.two_mul_div_two_add_one_of_odd hOdd).symm
              have hN1 : N + 1 = 2 * (m + 1) := by omega
              constructor
              · simpa [hN] using hcore_m.2.2.1
              · constructor
                · simpa [hN1] using hcore_ms.1
                · constructor
                  · have hfirst :
                      SameP1Vec
                        (XOnly.diffAddOrInfVec (E := W⁄k)
                          (XOnly.xLadderPair (E := W⁄k) x m).1
                          (XOnly.xLadderPair (E := W⁄k) x m).2
                          (XOnly.xAffVec x))
                        (xPair W (N : ℤ) x) := by
                      simpa [hN] using hadd
                    simpa [XOnly.xLadderPair, N, m, hEven] using hfirst
                  · have hsecond :
                      SameP1Vec
                        (XOnly.doubleVec (E := W⁄k)
                          (XOnly.xLadderPair (E := W⁄k) x m).2)
                        (xPair W ((N + 1 : ℕ) : ℤ) x) := by
                      simpa [hN1] using hdouble₁
                    simpa [XOnly.xLadderPair, N, m, hEven] using hsecond

/-- Missing Mathlib/repo EDS fact: for an elliptic curve, the univariate division-polynomial
representative has no zero-vector specialization and agrees with the corrected Montgomery-pair
ladder.  The first conjunct is the no-common-root/coprimality statement for `Φₙ` and `ΨSqₙ`;
the second conjunct is the EDS recurrence compatibility with `doubleVec` and `diffAddOrInfVec`. -/
public theorem xPair_ne_zero_and_same_xLadderRep_EDS
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
      xPair W (n : ℤ) x ≠ 0 ∧
      SameP1Vec
        (XOnly.xLadderRep (E := W⁄k) x n)
        (xPair W (n : ℤ) x) := by
    have h := xLadderPair_same_xPair_EDS (W := W) n x h4 hψ_ne hc3
    exact ⟨h.1, by simpa [XOnly.xLadderRep] using h.2.2.1⟩

/-- No common root for the two coordinates of the division-polynomial x-representative. -/
public theorem xPair_ne_zero_of_isElliptic
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    xPair W (n : ℤ) x ≠ 0 :=
  (xPair_ne_zero_and_same_xLadderRep_EDS (W := W) n x h4 hψ_ne hc3).1

/-- Evaluation form of coprimality: `Φₙ(x)` and `ΨSqₙ(x)` do not vanish together on an
elliptic curve. -/
public theorem Φ_ΨSq_no_common_eval_zero
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    ¬ ((W.Φ (n : ℤ)).eval x = 0 ∧ (W.ΨSq (n : ℤ)).eval x = 0) := by
  intro h
  exact xPair_ne_zero_of_isElliptic (W := W) n x h4 hψ_ne hc3 (by
    ext i <;> fin_cases i
    · simpa only [xPair, Fin.zero_eta, Matrix.cons_val_zero, Pi.zero_apply] using h.1
    · simpa only [xPair, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Pi.zero_apply] using h.2)

/-- Sanity check: the EDS representative agrees with the ladder at `n = 3`.  The
`δ = 0` branch uses the elliptic no-common-root statement for `Φ₃` and `ΨSq₃`; the
non-degenerate branch is a direct polynomial identity. -/
public theorem xPair_same_xLadderRep_three
    (W : WeierstrassCurve k) [W.IsElliptic] (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec
      (XOnly.xLadderRep (E := W⁄k) x 3)
      (xPair W (3 : ℤ) x) := by
  classical
  let A : Fin 2 → k := XOnly.xAffVec x
  let B : Fin 2 → k := XOnly.doubleVec (E := W⁄k) A
  have hdelta : XOnly.deltaVec A B = W.Ψ₃.eval x := by
    simp [A, B, XOnly.deltaVec, XOnly.doubleVec, XOnly.dupNumH, XOnly.dupDenH,
      XOnly.xAffVec, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq,
      WeierstrassCurve.baseChange]
    ring
  rw [XOnly.xLadderRep_three]
  change SameP1Vec (XOnly.diffAddOrInfVec (W⁄k) A B A) (xPair W (3 : ℤ) x)
  unfold XOnly.diffAddOrInfVec
  by_cases hδ : XOnly.deltaVec A B = 0
  · simp [hδ]
    have hψ3 : W.Ψ₃.eval x = 0 := by
      simpa [hdelta] using hδ
    have hsecond : (W.ΨSq (3 : ℤ)).eval x = 0 := by
      rw [WeierstrassCurve.ΨSq_three]
      simp [hψ3]
    have hfirst : (W.Φ (3 : ℤ)).eval x ≠ 0 := by
      intro hfirst
      exact Φ_ΨSq_no_common_eval_zero (W := W) 3 x h4 hψ_ne hc3
        ⟨by simpa using hfirst, by simpa using hsecond⟩
    refine SameP1Vec.mk_vec
      (u := XOnly.xInfVec) (v := xPair W (3 : ℤ) x)
      (c := (W.Φ (3 : ℤ)).eval x) hfirst ?_ ?_
    · simp [xPair, XOnly.xInfVec]
    · simpa [xPair, XOnly.xInfVec] using hsecond
  · simp [hδ]
    refine SameP1Vec.mk_vec
      (u := XOnly.diffAddVec (W⁄k) A B A) (v := xPair W (3 : ℤ) x)
      (c := 1) one_ne_zero ?_ ?_
    · simp [A, B, xPair, XOnly.diffAddVec, XOnly.sumNumVec, XOnly.deltaVec,
        XOnly.doubleVec, XOnly.dupNumH, XOnly.dupDenH, XOnly.xAffVec,
        WeierstrassCurve.Φ_three, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
        WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.baseChange]
      ring
    · simp [A, B, xPair, XOnly.diffAddVec, XOnly.deltaVec, XOnly.doubleVec,
        XOnly.dupNumH, XOnly.dupDenH, XOnly.xAffVec, WeierstrassCurve.ΨSq_three,
        WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.baseChange]
      ring

/-- Sanity check: the EDS representative agrees with the ladder at `n = 4`. -/
public theorem xPair_same_xLadderRep_four (W : WeierstrassCurve k) (x : k) :
    SameP1Vec
      (XOnly.xLadderRep (E := W⁄k) x 4)
      (xPair W (4 : ℤ) x) := by
  rw [XOnly.xLadderRep_four]
  refine SameP1Vec.mk_vec
    (u := XOnly.doubleVec (W⁄k) (XOnly.doubleVec (W⁄k) (XOnly.xAffVec x)))
    (v := xPair W (4 : ℤ) x) (c := 1) one_ne_zero ?_ ?_
  · simp [xPair, XOnly.doubleVec, XOnly.dupNumH, XOnly.dupDenH, XOnly.xAffVec,
      WeierstrassCurve.Φ_four, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.baseChange]
    ring
  · simp [xPair, XOnly.doubleVec, XOnly.dupNumH, XOnly.dupDenH, XOnly.xAffVec,
      WeierstrassCurve.ΨSq_four, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.baseChange]
    ring

/-- Irreducible remaining EDS recurrence seam: the corrected Montgomery-pair ladder agrees
with the `[Φₙ, ΨSqₙ]` division-polynomial representative. -/
public theorem xPair_same_xLadderRep_seam_EDS_core
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec
      (XOnly.xLadderRep (E := W⁄k) x n)
      (xPair W (n : ℤ) x) :=
  (xPair_ne_zero_and_same_xLadderRep_EDS (W := W) n x h4 hψ_ne hc3).2

/-- SEAM: the EDS/division-polynomial compatibility of the raw x-only ladder. -/
public theorem xPair_same_xLadderRep_seam
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec
      (XOnly.xLadderRep (E := W⁄k) x n)
      (xPair W (n : ℤ) x) :=
  xPair_same_xLadderRep_seam_EDS_core (W := W) n x h4 hψ_ne hc3

/-- The projective division-polynomial coordinate formula assembled from the ladder seams. -/
public theorem xRep_nsmul_same_xPair (W : WeierstrassCurve k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0)
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    SameP1Vec
      ((n • (Point.some x y h : (W⁄k).Point)).xRep)
      (xPair W (n : ℤ) x) := by
  exact SameP1Vec.trans
    (XOnly.xLadderRep_correct_seam (E := W⁄k) h n)
    (xPair_same_xLadderRep_seam (W := W) n x h4 hψ_ne hc3)

/-- Keystone target reduced to the projective division-polynomial coordinate formula. -/
public theorem nsmul_eq_zero_iff_ΨSq_eval (W : WeierstrassCurve k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0)
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.ΨSq (n : ℤ)).eval x = 0 := by
  classical
  let P : (W⁄k).Point := Point.some x y h
  constructor
  · intro hn
    have hsame :
        SameP1Vec ((n • P).xRep) (xPair W (n : ℤ) x) :=
      xRep_nsmul_same_xPair (W := W) h4 hψ_ne hc3 (n := n) h
    have hsecond :=
      SameP1Vec.second_eq_zero_of_same_infty (v := xPair W (n : ℤ) x) (by
        simpa [P, hn] using hsame)
    simpa [xPair] using hsecond
  · intro hψ
    by_contra hn
    cases hnp : n • P with
    | zero =>
        exact hn hnp
    | some xn yn hnonsing =>
        have hsame :
            SameP1Vec ((n • P).xRep) (xPair W (n : ℤ) x) :=
          xRep_nsmul_same_xPair (W := W) h4 hψ_ne hc3 (n := n) h
        have hsecond_ne :
            (xPair W (n : ℤ) x) 1 ≠ 0 :=
          SameP1Vec.second_ne_zero_of_same_affine
            (x := xn) (v := xPair W (n : ℤ) x) (by
              simpa [hnp] using hsame)
        exact hsecond_ne (by simpa [xPair] using hψ)

end KeystoneLadder

