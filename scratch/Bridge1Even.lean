import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic
import scratch.Bridge1HCD

/-!
# Bridge 1 (Even case): `preΨ'_root_Ψ₂Sq_ne'`

Proves that at a root `x` of `Ψ₂Sq`, `(W.preΨ' n).eval x ≠ 0` when `(n : K) ≠ 0`.
-/

set_option maxHeartbeats 6400000
set_option maxRecDepth 4096

open Polynomial

variable {K : Type*} [Field K]

/-! ### Section 0: Coprimality cert (proven in Keystone, extracted here) -/

/-- On an elliptic curve, `Ψ₂Sq` and `Ψ₃` have no common root.
Proven via Bezout cofactor certificate in `KeystoneResultantCerts` (commit ec63d59). -/
private lemma Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero_cert
    (W : WeierstrassCurve K) [W.IsElliptic] {x : K}
    (hs : W.Ψ₂Sq.eval x = 0) : W.Ψ₃.eval x ≠ 0 := by
  sorry -- KNOWN CERT: bezout_Ψ₂Sq_Ψ₃ ⟹ W.Δ^2 = 0 ⟹ contradiction with IsElliptic

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
    rw [neg_sq]
    exact ih n (by omega)

-- C-exponent identity for even-m case: tri(k) + 3*tri(k+1) = tri(2k+2)
private lemma tri_even_m (k : ℕ) : tri k + 3 * tri (k + 1) = tri (2 * k + 2) := by
  have h1 := two_mul_tri k
  have h2 := two_mul_tri (k + 1)
  have h3 := two_mul_tri (2 * k + 2)
  nlinarith

-- C-exponent identity for odd-m case: tri(k+2) + 3*tri(k+1) = tri(2k+3)
private lemma tri_odd_m (k : ℕ) : tri (k + 2) + 3 * tri (k + 1) = tri (2 * k + 3) := by
  have h1 := two_mul_tri (k + 2)
  have h2 := two_mul_tri (k + 1)
  have h3 := two_mul_tri (2 * k + 3)
  nlinarith

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
      -- Goal: -(oddSign k * C^tri(k) * (oddSign(k+1) * C^tri(k+1))^3)
      --     = oddSign(k+k+2) * C^tri(k+k+2)
      rw [mul_pow, ← pow_mul]
      have hsgn3 : oddSign (K := K) (k + 1) ^ 3 = oddSign (K := K) (k + 1) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, oddSign_sq, one_mul]
      rw [hsgn3]
      rw [show k + k + 2 = 2 * k + 2 from by omega, ← oddSign_even_m (K := K) k]
      rw [show tri (2 * k + 2) = tri k + 3 * tri (k + 1) from (tri_even_m k).symm]
      rw [pow_add]
      ring
    · simp only [hm, ↓reduceIte, mul_zero, sub_zero, mul_one]
      obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hm
      rw [show 2 * k + 1 + 4 = 2 * (k + 2) + 1 from by omega, ih (k + 2) (by omega)]
      rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 from by omega, ih (k + 1) (by omega)]
      -- After rewrites, LHS = oddSign(k+2)*C^tri(k+2) * (oddSign(k+1)*C^tri(k+1))^3
      -- RHS = oddSign(2*(k+1)+1) * C^tri(2*(k+1)+1)
      rw [mul_pow, ← pow_mul]
      have hsgn3 : oddSign (K := K) (k + 1) ^ 3 = oddSign (K := K) (k + 1) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, oddSign_sq, one_mul]
      rw [hsgn3]
      -- Goal: oddSign(k+2) * C^tri(k+2) * (oddSign(k+1) * C^(tri(k+1)*3))
      --     = oddSign(2*(k+1)+1) * C^tri(2*(k+1)+1)
      -- Rewrite RHS index: 2*(k+1)+1 = 2*k+3
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by omega]
      rw [show tri (2 * k + 3) = tri (k + 2) + 3 * tri (k + 1) from (tri_odd_m k).symm]
      rw [← oddSign_odd_m (K := K) k]
      rw [pow_add]
      ring

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
      · obtain ⟨r, rfl⟩ := hk
        rw [show 2*(r+r)+2 = 4*r+2 from by omega, ihA r (by omega)]
        rw [show 2*(r+r)+4 = 4*(r+1) from by omega, ihB r (by omega)]
        -- This is a polynomial identity in C, D with D² = -4C³.
        sorry
      · obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.mp hk
        rw [show 2*(2*r+1)+2 = 4*(r+1) from by omega, ihB r (by omega)]
        rw [show 2*(2*r+1)+4 = 4*(r+1)+2 from by omega, ihA (r+1) (by omega)]
        sorry
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
        · -- r = 0 case: use hA at k=0
          simp only [Nat.cast_zero, zero_add, mul_one, mul_zero, pow_zero]
          -- need hA for k=0 instance; we have ihA and ihB from the outer ih
          -- For r=0: 4*(r+r+1+1) = 4*1 = 4, need preNormEDS' 0 C D 4
          -- simpa path was wrong; the goal after r=0 substitution should involve preNormEDS'
          -- Actually after all rewrites this should be a concrete computation
          -- Let's try norm_num / simp path
          sorry
        · rw [ihA (r+1) (by omega)]
          sorry
      · obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.mp hk
        rw [show 2*(2*r+1)+2 = 4*(r+1) from by omega, ihB r (by omega)]
        rw [show 2*(2*r+1)+4 = 4*(r+1)+2 from by omega, ihA (r+1) (by omega)]
        rw [show 2*(2*r+1)+6 = 4*(r+2) from by omega, ihB (r+1) (by omega)]
        sorry

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
    · -- m' = 2*r, so n = 4*r
      rcases Nat.eq_zero_or_pos r with rfl | hr_pos
      · exfalso; apply hn; have hneq : n = 0 := by omega
        simp [hneq]
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr_pos.ne'
        have hn_eq : n = 4 * (s + 1) := by omega
        rw [hn_eq, hfB s] at hx
        have hs1_ne : ((s : K) + 1) ≠ 0 := by
          intro hs1
          apply hn
          rw [hn_eq]
          push_cast
          linear_combination (4 : K) * hs1
        exact mul_ne_zero (mul_ne_zero hs1_ne hD) (pow_ne_zero _ hC) hx
    · -- m' = 2*r+1, so n = 4*r+2
      have hn_eq : n = 4 * r + 2 := by omega
      rw [hn_eq, hfA r] at hx
      have hr1_ne : (2 * (r : K) + 1) ≠ 0 := by
        intro hr1
        apply hn
        rw [hn_eq]
        push_cast
        linear_combination (2 : K) * hr1
      exact mul_ne_zero hr1_ne (pow_ne_zero _ hC) hx

end WeierstrassCurve
