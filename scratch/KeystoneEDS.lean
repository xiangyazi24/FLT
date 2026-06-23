import scratch.KeystoneSameP1

/-! # Keystone avenue (d): EDS core discharge (relocated above SameP1 + Coprimality).
The core `xPair_double_and_diffAddOrInf_EDS_core` is proven here (NOT in KeystoneLadder,
which is Mathlib-only and below the wiring) from the non-circular no-common-root lemmas
(KeystoneCoprimality) + the SameP1 wiring (KeystoneSameP1), threading (h4, hψ_ne, hc3). -/

open Polynomial WeierstrassCurve
open scoped Classical

variable {k : Type*} [Field k]

namespace KeystoneLadder
namespace XOnly

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

end XOnly
end KeystoneLadder
