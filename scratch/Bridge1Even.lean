import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic
import scratch.Bridge1HCD
import scratch.KeystoneResultantCerts

/-!
# Bridge 1 (Even case): `preΨ'_root_Ψ₂Sq_ne'`

Proves that at a root `x` of `Ψ₂Sq`, `(W.preΨ' n).eval x ≠ 0` when `(n : K) ≠ 0`.
-/

set_option maxHeartbeats 12800000
set_option maxRecDepth 4096

open Polynomial

variable {K : Type*} [Field K]

/-! ### Section 0: Coprimality cert -/

private lemma Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero_cert
    (W : WeierstrassCurve K) [W.IsElliptic] {x : K}
    (hs : W.Ψ₂Sq.eval x = 0) : W.Ψ₃.eval x ≠ 0 :=
  WeierstrassCurve.Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero W hs

/-! ### Section 1: Eval lemma -/

private lemma eval_preΨ'_at_Ψ₂Sq_root (W : WeierstrassCurve K) {x : K}
    (hs : W.Ψ₂Sq.eval x = 0) (n : ℕ) :
    (W.preΨ' n).eval x = preNormEDS' (0 : K) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n := by
  rw [WeierstrassCurve.preΨ']
  change (Polynomial.evalRingHom x) (preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n) =
    preNormEDS' 0 (W.Ψ₃.eval x) (W.preΨ₄.eval x) n
  rw [map_preNormEDS']
  simp [Polynomial.coe_evalRingHom, Polynomial.eval_pow, hs]

/-! ### Section 2: Odd nonvanishing -/

private theorem odd_ne_zero (C D : K) (hC : C ≠ 0) :
    ∀ N : ℕ, ¬Even N → preNormEDS' (0 : K) C D N ≠ 0 := by
  intro N
  induction N using normEDSRec' with
  | zero => intro hodd; exact absurd ⟨0, rfl⟩ hodd
  | one  => intro _; simp [preNormEDS'_one]
  | two  => intro hodd; exact absurd ⟨1, rfl⟩ hodd
  | three => intro _; simpa [preNormEDS'_three]
  | four => intro hodd; exact absurd ⟨2, rfl⟩ hodd
  | even m _ih => intro hodd; exact absurd ⟨m + 3, by omega⟩ hodd
  | odd m ih =>
    intro hodd
    rw [preNormEDS'_odd]
    by_cases hm : Even m
    · simp only [hm, ↓reduceIte, mul_zero, zero_sub, mul_one]
      intro heq
      have hmul_zero := neg_injective (heq.trans neg_zero.symm)
      exact absurd hmul_zero <| mul_ne_zero
          (ih (m+1) (by omega) (by obtain ⟨k, rfl⟩ := hm; exact fun ⟨j, hj⟩ => by omega))
          (pow_ne_zero _ (ih (m+3) (by omega)
              (by obtain ⟨k, rfl⟩ := hm; exact fun ⟨j, hj⟩ => by omega)))
    · simp only [hm, ↓reduceIte, mul_one, mul_zero, sub_zero]
      apply mul_ne_zero
      · apply ih (m + 4) (by omega)
        rw [Nat.not_even_iff_odd] at hm; obtain ⟨k, rfl⟩ := hm
        exact fun ⟨j, hj⟩ => by omega
      · apply pow_ne_zero; apply ih (m + 2) (by omega)
        rw [Nat.not_even_iff_odd] at hm; obtain ⟨k, rfl⟩ := hm
        exact fun ⟨j, hj⟩ => by omega

/-! ### Section 3: Odd closed form helpers -/

private def tri : ℕ → ℕ
  | 0 => 0
  | (m + 1) => tri m + (m + 1)

private lemma two_mul_tri (m : ℕ) : 2 * tri m = m * (m + 1) := by
  induction m with
  | zero => simp [tri]
  | succ m ih => simp only [tri]; linarith

private def oddSign : ℕ → K
  | 0 => 1
  | 1 => 1
  | (m + 2) => -(oddSign m)

private lemma oddSign_ne_zero : ∀ m : ℕ, oddSign (K := K) m ≠ 0 := by
  intro m; induction m using Nat.strongRecOn with | ind m ih => ?_
  match m with
  | 0 => simp [oddSign]
  | 1 => simp [oddSign]
  | m + 2 =>
    show -(oddSign (K := K) m) ≠ 0
    exact neg_ne_zero.mpr (ih m (by omega))

private lemma oddSign_double_eq (n : ℕ) :
    oddSign (K := K) (2 * n) = oddSign (K := K) (2 * n + 1) := by
  induction n with
  | zero => simp [oddSign]
  | succ n ih =>
    show oddSign (K := K) (2 * n + 2) = oddSign (K := K) (2 * n + 2 + 1)
    have h1 : oddSign (K := K) (2 * n + 2) = -(oddSign (2 * n)) := rfl
    have h2 : oddSign (K := K) (2 * n + 2 + 1) = -(oddSign (2 * n + 1)) := by
      show oddSign (K := K) ((2 * n + 1) + 2) = -(oddSign (2 * n + 1)); rfl
    rw [h1, h2, ih]

private lemma oddSign_mul_succ (k : ℕ) :
    oddSign (K := K) k * oddSign (K := K) (k + 1) = oddSign (K := K) (2 * k) := by
  induction k with
  | zero => simp [oddSign]
  | succ k ih =>
    show oddSign (K := K) (k + 1) * oddSign (K := K) (k + 2) = oddSign (K := K) (2 * k + 2)
    have hk2 : oddSign (K := K) (k + 2) = -(oddSign k) := rfl
    have h2k2 : oddSign (K := K) (2 * k + 2) = -(oddSign (2 * k)) := rfl
    rw [hk2, h2k2, mul_neg, neg_eq_iff_eq_neg, neg_neg, mul_comm]; exact ih

private lemma oddSign_even_m (k : ℕ) :
    -(oddSign (K := K) k * oddSign (K := K) (k + 1)) = oddSign (K := K) (2 * k + 2) := by
  rw [oddSign_mul_succ]; show -(oddSign (K := K) (2 * k)) = oddSign (K := K) (2 * k + 2); rfl

private lemma oddSign_odd_m (k : ℕ) :
    oddSign (K := K) (k + 2) * oddSign (K := K) (k + 1) = oddSign (K := K) (2 * k + 3) := by
  have hk2 : oddSign (K := K) (k + 2) = -(oddSign k) := rfl
  rw [hk2, neg_mul, oddSign_mul_succ]
  have h1 : -(oddSign (K := K) (2 * k)) = oddSign (K := K) (2 * k + 2) := rfl
  rw [h1]; exact oddSign_double_eq (k + 1)

private lemma oddSign_sq (n : ℕ) : oddSign (K := K) n ^ 2 = 1 := by
  induction n using Nat.strongRecOn with | ind n ih => ?_
  match n with
  | 0 => simp [oddSign]
  | 1 => simp [oddSign]
  | n + 2 =>
    show (-(oddSign (K := K) n)) ^ 2 = 1
    rw [neg_sq]; exact ih n (by omega)

private lemma oddSign_4r2 (r : ℕ) : oddSign (K := K) (4 * r + 2) = -1 := by
  induction r with
  | zero => simp [oddSign]
  | succ r ih =>
    show -(-(oddSign (K := K) (4 * r + 2))) = -1
    rw [neg_neg, ih]

private lemma oddSign_4r (r : ℕ) : oddSign (K := K) (4 * r) = 1 := by
  induction r with
  | zero => simp [oddSign]
  | succ r ih =>
    show -(-(oddSign (K := K) (4 * r))) = 1
    rw [neg_neg, ih]

private lemma tri_even_m (k : ℕ) : tri k + 3 * tri (k + 1) = tri (2 * k + 2) := by
  have h1 := two_mul_tri k; have h2 := two_mul_tri (k + 1); have h3 := two_mul_tri (2 * k + 2); nlinarith

private lemma tri_odd_m (k : ℕ) : tri (k + 2) + 3 * tri (k + 1) = tri (2 * k + 3) := by
  have h1 := two_mul_tri (k + 2); have h2 := two_mul_tri (k + 1); have h3 := two_mul_tri (2 * k + 3); nlinarith

/-! ### Section 3b: Odd closed form proof -/

private theorem odd_closed_form (C D : K) :
    ∀ m : ℕ, preNormEDS' (0 : K) C D (2 * m + 1) = oddSign (K := K) m * C ^ tri m := by
  intro m; induction m using Nat.strongRecOn with | ind m ih => ?_
  match m with
  | 0 => simp [preNormEDS'_one, tri, oddSign]
  | 1 => simp [show 2 * 1 + 1 = 3 from rfl, preNormEDS'_three, tri, oddSign]
  | m + 2 =>
    rw [show 2 * (m + 2) + 1 = 2 * (m + 0 + 2) + 1 from by ring, preNormEDS'_odd]
    by_cases hm : Even m
    · simp only [hm, ↓reduceIte, mul_zero, zero_sub, mul_one]
      obtain ⟨k, rfl⟩ := hm
      rw [show k + k + 1 = 2 * k + 1 from by omega, ih k (by omega)]
      rw [show k + k + 3 = 2 * (k + 1) + 1 from by omega, ih (k + 1) (by omega)]
      rw [mul_pow, ← pow_mul]
      have hsgn3 : oddSign (K := K) (k + 1) ^ 3 = oddSign (K := K) (k + 1) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, oddSign_sq, one_mul]
      rw [hsgn3, show k + k + 2 = 2 * k + 2 from by omega, ← oddSign_even_m (K := K) k]
      rw [show tri (2 * k + 2) = tri k + 3 * tri (k + 1) from (tri_even_m k).symm, pow_add]; ring
    · simp only [hm, ↓reduceIte, mul_zero, sub_zero, mul_one]
      obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hm
      rw [show 2 * k + 1 + 4 = 2 * (k + 2) + 1 from by omega, ih (k + 2) (by omega)]
      rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 from by omega, ih (k + 1) (by omega)]
      rw [mul_pow, ← pow_mul]
      have hsgn3 : oddSign (K := K) (k + 1) ^ 3 = oddSign (K := K) (k + 1) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, oddSign_sq, one_mul]
      rw [hsgn3, show 2 * (k + 1) + 1 = 2 * k + 3 from by omega]
      rw [show tri (2 * k + 3) = tri (k + 2) + 3 * tri (k + 1) from (tri_odd_m k).symm]
      rw [← oddSign_odd_m (K := K) k, pow_add]; ring

/-! ### Section 4: D ≠ 0 at Ψ₂Sq-root -/

private lemma preΨ₄_eval_ne_zero (W : WeierstrassCurve K) [W.IsElliptic] {x : K}
    (hs : W.Ψ₂Sq.eval x = 0) (h4 : (4 : K) ≠ 0) : W.preΨ₄.eval x ≠ 0 := by
  intro hD
  have hC := Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero_cert W hs
  have hCD := WeierstrassCurve.preΨ₄_sq_add_four_Ψ₃_cube_eq_zero_of_Ψ₂Sq_root W hs
  rw [hD, zero_pow two_ne_zero, zero_add] at hCD
  exact hC (pow_eq_zero_iff three_ne_zero |>.mp ((mul_eq_zero.mp hCD).resolve_left h4))

/-! ### Section 5: Even closed forms -/

private theorem even_closed_forms {C D : K} (hC : C ≠ 0)
    (hCD : D ^ 2 + 4 * C ^ 3 = 0) :
    (∀ k : ℕ, preNormEDS' (0 : K) C D (4 * k + 2) =
        (2 * (k : K) + 1) * C ^ (2 * k * (k + 1))) ∧
    (∀ k : ℕ, preNormEDS' (0 : K) C D (4 * (k + 1)) =
        ((k : K) + 1) * D * C ^ (2 * k * (k + 2))) := by
  have hDsq : D ^ 2 = -(4 * C ^ 3) := by linear_combination hCD
  suffices h : ∀ k : ℕ,
      (preNormEDS' (0 : K) C D (4 * k + 2) = (2 * (k : K) + 1) * C ^ (2 * k * (k + 1))) ∧
      (preNormEDS' (0 : K) C D (4 * (k + 1)) = ((k : K) + 1) * D * C ^ (2 * k * (k + 2))) by
    exact ⟨fun k => (h k).1, fun k => (h k).2⟩
  intro k
  induction k using Nat.strongRecOn with | ind k ih => ?_
  have ihA : ∀ j < k, preNormEDS' (0:K) C D (4*j+2) = (2*(j:K)+1)*C^(2*j*(j+1)) :=
    fun j hj => (ih j hj).1
  have ihB : ∀ j < k, preNormEDS' (0:K) C D (4*(j+1)) = ((j:K)+1)*D*C^(2*j*(j+2)) :=
    fun j hj => (ih j hj).2
  have hD2 : D ^ 2 = -4 * C ^ 3 := by linear_combination hCD
  have hA : preNormEDS' (0:K) C D (4*k+2) = (2*(k:K)+1)*C^(2*k*(k+1)) := by
    match k with
    | 0 => simp [preNormEDS'_two]
    | (k + 1) =>
      rw [show 4*(k+1)+2 = 2*(2*k+0+3) from by omega, preNormEDS'_even]
      rw [show 2*k+0+1 = 2*k+1 from by omega,
          show 2*k+0+3 = 2*(k+1)+1 from by omega,
          show 2*k+0+5 = 2*(k+2)+1 from by omega]
      rw [odd_closed_form C D k, odd_closed_form C D (k+1), odd_closed_form C D (k+2)]
      rw [show 2*k+0+2 = 2*k+2 from by omega, show 2*k+0+4 = 2*k+4 from by omega]
      by_cases hk : Even k
      · -- hA even-k case
        obtain ⟨r, rfl⟩ := hk
        rw [show 2*(r+r)+2 = 4*r+2 from by omega, ihA r (by omega)]
        rw [show 2*(r+r)+4 = 4*(r+1) from by omega, ihB r (by omega)]
        ring_nf; rw [hD2]
        have h_os1 : oddSign (K := K) (1 + r * 2) * oddSign (K := K) (r * 2) = 1 := by
          have : oddSign (K := K) (r * 2) = oddSign (K := K) (1 + r * 2) := by
            rw [show r * 2 = 2 * r from by ring, show 1 + 2 * r = 2 * r + 1 from by omega]
            exact oddSign_double_eq r
          rw [this, ← sq, oddSign_sq]
        have h_os2 : oddSign (K := K) (1 + r * 2) * oddSign (K := K) (2 + r * 2) = -1 := by
          rw [show 1 + r * 2 = 2 * r + 1 from by omega,
              show 2 + r * 2 = (2 * r + 1) + 1 from by omega,
              oddSign_mul_succ, show 2 * (2 * r + 1) = 4 * r + 2 from by omega, oddSign_4r2]
        have hcA : C ^ (r * 4) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (2 + r * 2) =
            C ^ (4 + r * 12 + r ^ 2 * 8) := by
          rw [← pow_add, ← pow_add, ← pow_add]; congr 1
          have := two_mul_tri (1 + r * 2); have := two_mul_tri (2 + r * 2); nlinarith
        have hcB : C ^ (r * 8) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (r * 2) * C ^ 3 =
            C ^ (4 + r * 12 + r ^ 2 * 8) := by
          rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1
          have := two_mul_tri (1 + r * 2); have := two_mul_tri (r * 2); nlinarith
        have hcR : C ^ 4 * C ^ (r * 12) * C ^ (r ^ 2 * 8) = C ^ (4 + r * 12 + r ^ 2 * 8) := by
          rw [← pow_add, ← pow_add]
        set P := C ^ (4 + r * 12 + r ^ 2 * 8)
        rw [hcR]
        have t1 : ↑r * C ^ (r * 4) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (2 + r * 2) *
            oddSign (K := K) (1 + r * 2) * oddSign (K := K) (2 + r * 2) * 4 = -(4 * ↑r * P) := by
          rw [show (↑r * C ^ (r * 4) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) *
            C ^ tri (2 + r * 2) * oddSign (1 + r * 2) * oddSign (2 + r * 2) * 4 : K) =
            4 * ↑r * (C ^ (r * 4) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (2 + r * 2)) *
            (oddSign (1 + r * 2) * oddSign (2 + r * 2)) from by ring]
          rw [h_os2, hcA]; ring
        have t2 : ↑r * C ^ (r * 8) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (r * 2) *
            oddSign (K := K) (1 + r * 2) * oddSign (K := K) (r * 2) * (-4 * C ^ 3) * 2 = -(8 * ↑r * P) := by
          rw [show (↑r * C ^ (r * 8) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (r * 2) *
            oddSign (1 + r * 2) * oddSign (r * 2) * (-4 * C ^ 3) * 2 : K) =
            -8 * ↑r * (oddSign (1 + r * 2) * oddSign (r * 2)) *
            (C ^ (r * 8) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (r * 2) * C ^ 3) from by ring]
          rw [h_os1, hcB]; ring
        have t3 : ↑r ^ 2 * C ^ (r * 4) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (2 + r * 2) *
            oddSign (K := K) (1 + r * 2) * oddSign (K := K) (2 + r * 2) * 4 = -(4 * ↑r ^ 2 * P) := by
          rw [show (↑r ^ 2 * C ^ (r * 4) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) *
            C ^ tri (2 + r * 2) * oddSign (1 + r * 2) * oddSign (2 + r * 2) * 4 : K) =
            4 * ↑r ^ 2 * (C ^ (r * 4) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (2 + r * 2)) *
            (oddSign (1 + r * 2) * oddSign (2 + r * 2)) from by ring]
          rw [h_os2, hcA]; ring
        have t4 : ↑r ^ 2 * C ^ (r * 8) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (r * 2) *
            oddSign (K := K) (1 + r * 2) * oddSign (K := K) (r * 2) * (-4 * C ^ 3) = -(4 * ↑r ^ 2 * P) := by
          rw [show (↑r ^ 2 * C ^ (r * 8) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (r * 2) *
            oddSign (1 + r * 2) * oddSign (r * 2) * (-4 * C ^ 3) : K) =
            -4 * ↑r ^ 2 * (oddSign (1 + r * 2) * oddSign (r * 2)) *
            (C ^ (r * 8) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (r * 2) * C ^ 3) from by ring]
          rw [h_os1, hcB]; ring
        have t5 : C ^ (r * 4) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (2 + r * 2) *
            oddSign (K := K) (1 + r * 2) * oddSign (K := K) (2 + r * 2) = -P := by
          rw [show (C ^ (r * 4) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (2 + r * 2) *
            oddSign (1 + r * 2) * oddSign (2 + r * 2) : K) =
            (C ^ (r * 4) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (2 + r * 2)) *
            (oddSign (1 + r * 2) * oddSign (2 + r * 2)) from by ring]
          rw [h_os2, hcA]; ring
        have t6 : C ^ (r * 8) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (r * 2) *
            oddSign (K := K) (1 + r * 2) * oddSign (K := K) (r * 2) * (-4 * C ^ 3) = -(4 * P) := by
          rw [show (C ^ (r * 8) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (r * 2) *
            oddSign (1 + r * 2) * oddSign (r * 2) * (-4 * C ^ 3) : K) =
            -4 * (oddSign (1 + r * 2) * oddSign (r * 2)) *
            (C ^ (r * 8) * C ^ (r ^ 2 * 4) * C ^ tri (1 + r * 2) * C ^ tri (r * 2) * C ^ 3) from by ring]
          rw [h_os1, hcB]; ring
        rw [t1, t2, t3, t4, t5, t6]; push_cast; ring
      · -- hA odd-k case
        obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.mp hk
        rw [show 2*(2*r+1)+2 = 4*(r+1) from by omega, ihB r (by omega)]
        rw [show 2*(2*r+1)+4 = 4*(r+1)+2 from by omega, ihA (r+1) (by omega)]
        -- Goal has oddSign at indices 2*r+1, 2*r+1+1, 2*r+1+2 (all in +form)
        have hos_pos : oddSign (K := K) (2 * r + 1 + 1) * oddSign (K := K) (2 * r + 1 + 2) = 1 := by
          rw [show 2 * r + 1 + 1 = 2 * (r + 1) from by omega,
              show 2 * r + 1 + 2 = 2 * (r + 1) + 1 from by omega,
              oddSign_mul_succ, show 2 * (2 * (r + 1)) = 4 * (r + 1) from by omega, oddSign_4r]
        have hos_neg : oddSign (K := K) (2 * r + 1) * oddSign (K := K) (2 * r + 1 + 1) = -1 := by
          rw [show 2 * r + 1 + 1 = (2 * r + 1) + 1 from by omega, oddSign_mul_succ,
              show 2 * (2 * r + 1) = 4 * r + 2 from by omega, oddSign_4r2]
        calc _ = (↑r + 1) ^ 2 * D ^ 2 * (C ^ (2 * r * (r + 2))) ^ 2 *
                    (oddSign (K := K) (2 * r + 1 + 1) * oddSign (K := K) (2 * r + 1 + 2)) *
                    (C ^ tri (2 * r + 1 + 1) * C ^ tri (2 * r + 1 + 2)) -
                  (oddSign (K := K) (2 * r + 1) * oddSign (K := K) (2 * r + 1 + 1)) *
                    (C ^ tri (2 * r + 1) * C ^ tri (2 * r + 1 + 1)) *
                    ((2 * (↑(r + 1) : K) + 1)) ^ 2 * (C ^ (2 * (r + 1) * (r + 1 + 1))) ^ 2 := by ring
             _ = _ := by
              rw [hos_pos, hos_neg, hD2, ← pow_mul, ← pow_mul]
              have hcA : C ^ 3 * C ^ (2 * r * (r + 2) * 2) *
                  C ^ tri (2 * r + 1 + 1) * C ^ tri (2 * r + 1 + 2) =
                  C ^ (2 * (2 * r + 1 + 1) * (2 * r + 1 + 1 + 1)) := by
                rw [← pow_add, ← pow_add, ← pow_add]; congr 1
                have := two_mul_tri (2 * r + 1 + 1); have := two_mul_tri (2 * r + 1 + 2); nlinarith
              have hcB : C ^ tri (2 * r + 1) * C ^ tri (2 * r + 1 + 1) *
                  C ^ (2 * (r + 1) * (r + 1 + 1) * 2) =
                  C ^ (2 * (2 * r + 1 + 1) * (2 * r + 1 + 1 + 1)) := by
                rw [← pow_add, ← pow_add]; congr 1
                have := two_mul_tri (2 * r + 1); have := two_mul_tri (2 * r + 1 + 1); nlinarith
              conv_lhs =>
                rw [show ((↑r + 1) ^ 2 * (-4 * C ^ 3) * C ^ (2 * r * (r + 2) * 2) * 1 *
                      (C ^ tri (2 * r + 1 + 1) * C ^ tri (2 * r + 1 + 2)) -
                    -1 * (C ^ tri (2 * r + 1) * C ^ tri (2 * r + 1 + 1)) *
                      (2 * ↑(r + 1) + 1) ^ 2 * C ^ (2 * (r + 1) * (r + 1 + 1) * 2) : K) =
                    (-(↑r + 1) ^ 2 * 4) *
                      (C ^ 3 * C ^ (2 * r * (r + 2) * 2) *
                        C ^ tri (2 * r + 1 + 1) * C ^ tri (2 * r + 1 + 2)) +
                    (2 * ↑(r + 1) + 1) ^ 2 *
                      (C ^ tri (2 * r + 1) * C ^ tri (2 * r + 1 + 1) *
                        C ^ (2 * (r + 1) * (r + 1 + 1) * 2))
                    from by ring]
              rw [hcA, hcB]; push_cast; ring
  constructor
  · exact hA
  · match k with
    | 0 => simp [preNormEDS'_four]
    | (k + 1) =>
      rw [show 4*(k+1+1) = 2*(2*k+1+3) from by omega, preNormEDS'_even]
      rw [show 2*k+1+2 = 2*(k+1)+1 from by omega,
          show 2*k+1+4 = 2*(k+2)+1 from by omega]
      rw [odd_closed_form C D (k+1), odd_closed_form C D (k+2)]
      rw [show 2*k+1+1 = 2*k+2 from by omega,
          show 2*k+1+3 = 2*k+4 from by omega,
          show 2*k+1+5 = 2*k+6 from by omega]
      by_cases hk : Even k
      · obtain ⟨r, rfl⟩ := hk
        rw [show 2*(r+r)+2 = 4*r+2 from by omega, ihA r (by omega)]
        rw [show 2*(r+r)+4 = 4*(r+1) from by omega, ihB r (by omega)]
        rw [show 2*(r+r)+6 = 4*(r+1)+2 from by omega]
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · -- hB even-k r=0: use hA to substitute preNormEDS' 0 C D 6
          rw [show 4 * (0 + 0 + 1) + 2 = 4 * 1 + 2 from by omega] at hA
          simp only [oddSign, tri] at *
          rw [hA]; ring
        · -- hB even-k r>0
          rw [ihA (r+1) (by omega)]
          simp only [mul_pow, oddSign_sq, one_mul]
          calc _ = D * ((2 * ↑(r + 1) + 1) * (↑r + 1) *
                        ((C ^ tri (r + r + 1)) ^ 2 * C ^ (2 * r * (r + 2)) *
                          C ^ (2 * (r + 1) * (r + 1 + 1))) -
                      (2 * ↑r + 1) * (↑r + 1) *
                        (C ^ (2 * r * (r + 1)) * C ^ (2 * r * (r + 2)) *
                          (C ^ tri (r + r + 2)) ^ 2)) := by ring
               _ = _ := by
                rw [← pow_mul C (tri (r + r + 1)) 2, ← pow_mul C (tri (r + r + 2)) 2]
                have hcA : C ^ (tri (r + r + 1) * 2) * C ^ (2 * r * (r + 2)) *
                    C ^ (2 * (r + 1) * (r + 1 + 1)) =
                    C ^ (2 * (r + r + 1) * (r + r + 1 + 2)) := by
                  rw [← pow_add, ← pow_add]; congr 1
                  have := two_mul_tri (r + r + 1); nlinarith
                have hcB : C ^ (2 * r * (r + 1)) * C ^ (2 * r * (r + 2)) *
                    C ^ (tri (r + r + 2) * 2) =
                    C ^ (2 * (r + r + 1) * (r + r + 1 + 2)) := by
                  rw [← pow_add, ← pow_add]; congr 1
                  have := two_mul_tri (r + r + 2); nlinarith
                rw [hcA, hcB]; push_cast; ring
      · -- hB odd-k
        obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.mp hk
        rw [show 2*(2*r+1)+2 = 4*(r+1) from by omega, ihB r (by omega)]
        rw [show 2*(2*r+1)+4 = 4*(r+1)+2 from by omega, ihA (r+1) (by omega)]
        rw [show 2*(2*r+1)+6 = 4*(r+2) from by omega, ihB (r+1) (by omega)]
        -- All oddSign terms are squared → = 1. D is a linear factor.
        simp only [mul_pow, oddSign_sq, one_mul]
        calc _ = D * ((2 * ↑(r + 1) + 1) * (↑(r + 1) + 1) *
                      ((C ^ tri (2 * r + 1 + 1)) ^ 2 * C ^ (2 * (r + 1) * (r + 1 + 1)) *
                        C ^ (2 * (r + 1) * (r + 1 + 2))) -
                    (↑r + 1) * (2 * ↑(r + 1) + 1) *
                      (C ^ (2 * r * (r + 2)) * C ^ (2 * (r + 1) * (r + 1 + 1)) *
                        (C ^ tri (2 * r + 1 + 2)) ^ 2)) := by ring
             _ = _ := by
              rw [← pow_mul C (tri (2 * r + 1 + 1)) 2, ← pow_mul C (tri (2 * r + 1 + 2)) 2]
              have hcA : C ^ (tri (2 * r + 1 + 1) * 2) * C ^ (2 * (r + 1) * (r + 1 + 1)) *
                  C ^ (2 * (r + 1) * (r + 1 + 2)) =
                  C ^ (2 * (2 * r + 1 + 1) * (2 * r + 1 + 1 + 2)) := by
                rw [← pow_add, ← pow_add]; congr 1
                have := two_mul_tri (2 * r + 1 + 1); nlinarith
              have hcB : C ^ (2 * r * (r + 2)) * C ^ (2 * (r + 1) * (r + 1 + 1)) *
                  C ^ (tri (2 * r + 1 + 2) * 2) =
                  C ^ (2 * (2 * r + 1 + 1) * (2 * r + 1 + 1 + 2)) := by
                rw [← pow_add, ← pow_add]; congr 1
                have := two_mul_tri (2 * r + 1 + 2); nlinarith
              rw [hcA, hcB]; push_cast; ring

/-! ### Section 6: Main theorem -/

namespace WeierstrassCurve

theorem preΨ'_root_Ψ₂Sq_ne' (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K} (hx : (W.preΨ' n).IsRoot x) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  intro hs
  rw [Polynomial.IsRoot] at hx
  rw [eval_preΨ'_at_Ψ₂Sq_root W hs n] at hx
  set C := W.Ψ₃.eval x
  set D := W.preΨ₄.eval x
  have hC : C ≠ 0 := Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero_cert W hs
  have hCD : D ^ 2 + 4 * C ^ 3 = 0 := preΨ₄_sq_add_four_Ψ₃_cube_eq_zero_of_Ψ₂Sq_root W hs
  rcases Nat.even_or_odd n with hne | hno
  swap
  · exact odd_ne_zero C D hC n (Nat.not_even_iff_odd.mpr hno) hx
  · have h2 : (2 : K) ≠ 0 := by
      intro h2; apply hn; obtain ⟨m', hm'⟩ := hne
      have : (n : K) = 2 * (m' : K) := by push_cast [hm']; ring
      rw [this, h2, zero_mul]
    have h4 : (4 : K) ≠ 0 := by
      intro h4; apply h2
      have : (2 : K) * 2 = 4 := by norm_num
      exact (mul_eq_zero.mp (by rw [this]; exact h4)).elim id id
    have hD : D ≠ 0 := preΨ₄_eval_ne_zero W hs h4
    obtain ⟨hfA, hfB⟩ := even_closed_forms hC hCD
    obtain ⟨m', hm'⟩ := hne
    rcases Nat.even_or_odd m' with ⟨r, hr⟩ | ⟨r, hr⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr_pos
      · exfalso; apply hn; have hneq : n = 0 := by omega
        simp [hneq]
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr_pos.ne'
        have hn_eq : n = 4 * (s + 1) := by omega
        rw [hn_eq, hfB s] at hx
        have hs1_ne : ((s : K) + 1) ≠ 0 := by
          intro hs1; apply hn; rw [hn_eq]; push_cast; linear_combination (4 : K) * hs1
        exact mul_ne_zero (mul_ne_zero hs1_ne hD) (pow_ne_zero _ hC) hx
    · have hn_eq : n = 4 * r + 2 := by omega
      rw [hn_eq, hfA r] at hx
      have hr1_ne : (2 * (r : K) + 1) ≠ 0 := by
        intro hr1; apply hn; rw [hn_eq]; push_cast; linear_combination (2 : K) * hr1
      exact mul_ne_zero hr1_ne (pow_ne_zero _ hC) hx

end WeierstrassCurve
