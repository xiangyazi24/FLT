import FLT.Assumptions.MazurProof.N18Mumford

/-!
# The fixed rank-two basis of the N18 affine ring

This is the coefficient API used by the oriented-ideal normal-form proof.
Every element is written uniquely as `p(x) + q(x)y`; no general matrix or
Hermite normal form is introduced.
-/

open Polynomial

namespace MazurProof.N18Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

def xClassHom : K[X] →+* CoordinateRing K :=
  AdjoinRoot.of (curvePoly K)

@[simp] theorem xClassHom_apply (p : K[X]) :
    xClassHom K p = xClass K p := rfl

@[simp] theorem xClass_zero : xClass K 0 = 0 := by
  exact map_zero (xClassHom K)

@[simp] theorem xClass_one : xClass K 1 = 1 := by
  exact map_one (xClassHom K)

@[simp] theorem xClass_add (p q : K[X]) :
    xClass K (p + q) = xClass K p + xClass K q := by
  exact map_add (xClassHom K) p q

@[simp] theorem xClass_sub (p q : K[X]) :
    xClass K (p - q) = xClass K p - xClass K q := by
  exact map_sub (xClassHom K) p q

@[simp] theorem xClass_neg (p : K[X]) :
    xClass K (-p) = -xClass K p := by
  exact map_neg (xClassHom K) p

@[simp] theorem xClass_mul (p q : K[X]) :
    xClass K (p * q) = xClass K p * xClass K q := by
  exact map_mul (xClassHom K) p q

@[simp] theorem xClass_pow (p : K[X]) (n : ℕ) :
    xClass K (p ^ n) = xClass K p ^ n := by
  exact map_pow (xClassHom K) p n

def normalPoly : CoordinateRing K →ₗ[K[X]] K[X][X] :=
  AdjoinRoot.modByMonicHom (curvePoly_monic K)

def coeff0 : CoordinateRing K →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 0).comp (normalPoly K)

def coeffY : CoordinateRing K →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 1).comp (normalPoly K)

@[simp] theorem normalPoly_mk (g : K[X][X]) :
    normalPoly K (mk K g) = g %ₘ curvePoly K := by
  rfl

@[simp] theorem coeff0_mk (g : K[X][X]) :
    coeff0 K (mk K g) = (g %ₘ curvePoly K).coeff 0 := by
  rfl

@[simp] theorem coeffY_mk (g : K[X][X]) :
    coeffY K (mk K g) = (g %ₘ curvePoly K).coeff 1 := by
  rfl

private theorem degree_curvePoly : (curvePoly K).degree = 2 := by
  rw [degree_eq_natDegree (curvePoly_monic K).ne_zero,
    curvePoly_natDegree]
  norm_num

theorem normalPoly_eq_C_add_C_mul_X (z : CoordinateRing K) :
    normalPoly K z = C (coeff0 K z) + C (coeffY K z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly K =
        C ((g %ₘ curvePoly K).coeff 0) +
          C ((g %ₘ curvePoly K).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly K) (curvePoly_monic K)
        (n := 2) (by rw [degree_curvePoly]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

theorem recompose (z : CoordinateRing K) :
    xClass K (coeff0 K z) + xClass K (coeffY K z) * yClass K = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        xClass K (coeff0 K (AdjoinRoot.mk (curvePoly K) g)) +
              xClass K (coeffY K (AdjoinRoot.mk (curvePoly K) g)) * yClass K =
            AdjoinRoot.mk (curvePoly K)
              (C (coeff0 K (AdjoinRoot.mk (curvePoly K) g)) +
                C (coeffY K (AdjoinRoot.mk (curvePoly K) g)) * X) := by
                  simp only [xClass, yClass, mk, map_add, map_mul,
                    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk (curvePoly K)
              (normalPoly K (AdjoinRoot.mk (curvePoly K) g)) := by
                rw [normalPoly_eq_C_add_C_mul_X]
        _ = AdjoinRoot.mk (curvePoly K) g :=
          AdjoinRoot.mk_leftInverse (curvePoly_monic K)
            (AdjoinRoot.mk (curvePoly K) g)

@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 K (xClass K p) = p := by
  change (C p %ₘ curvePoly K).coeff 0 = p
  rw [(modByMonic_eq_self_iff (curvePoly_monic K)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)

@[simp] theorem coeffY_xClass (p : K[X]) :
    coeffY K (xClass K p) = 0 := by
  change (C p %ₘ curvePoly K).coeff 1 = 0
  rw [(modByMonic_eq_self_iff (curvePoly_monic K)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)

@[simp] theorem coeff0_yClass : coeff0 K (yClass K) = 0 := by
  change (X %ₘ curvePoly K).coeff 0 = 0
  rw [(modByMonic_eq_self_iff (curvePoly_monic K)).mpr]
  · simp
  · rw [degree_X, degree_curvePoly]
    norm_num

@[simp] theorem coeffY_yClass : coeffY K (yClass K) = 1 := by
  change (X %ₘ curvePoly K).coeff 1 = 1
  rw [(modByMonic_eq_self_iff (curvePoly_monic K)).mpr]
  · simp
  · rw [degree_X, degree_curvePoly]
    norm_num

theorem eq_iff_coeff (z w : CoordinateRing K) :
    z = w ↔ coeff0 K z = coeff0 K w ∧ coeffY K z = coeffY K w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose K z, ← recompose K w, h0, hY]

/-! ## Hyperelliptic conjugation and the quadratic norm -/

private theorem neg_y_relation :
    (curvePoly K).eval₂ (AdjoinRoot.of (curvePoly K)) (-(yClass K)) = 0 := by
  change (X ^ 2 - C (f K)).eval₂
      (AdjoinRoot.of (curvePoly K)) (-(yClass K)) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change (-(yClass K)) ^ 2 - xClass K (f K) = 0
  rw [neg_sq, yClass_sq]
  exact sub_self _

def conjugate : CoordinateRing K →+* CoordinateRing K :=
  AdjoinRoot.lift (AdjoinRoot.of (curvePoly K)) (-(yClass K))
    (neg_y_relation K)

@[simp] theorem conjugate_xClass (p : K[X]) :
    conjugate K (xClass K p) = xClass K p := by
  change conjugate K (AdjoinRoot.of (curvePoly K) p) =
    AdjoinRoot.of (curvePoly K) p
  exact AdjoinRoot.lift_of (neg_y_relation K)

@[simp] theorem conjugate_yClass :
    conjugate K (yClass K) = -(yClass K) := by
  exact AdjoinRoot.lift_root (neg_y_relation K)

theorem conjugate_involutive : Function.Involutive (conjugate K) := by
  have hcomp : (conjugate K).comp (conjugate K) =
      RingHom.id (CoordinateRing K) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro k
        change conjugate K (conjugate K (xClass K (C k))) = xClass K (C k)
        rw [conjugate_xClass, conjugate_xClass]
      · change conjugate K (conjugate K (xClass K X)) = xClass K X
        rw [conjugate_xClass, conjugate_xClass]
    · change conjugate K (conjugate K (yClass K)) = yClass K
      rw [conjugate_yClass, map_neg, conjugate_yClass, neg_neg]
  intro z
  exact DFunLike.congr_fun hcomp z

def norm (z : CoordinateRing K) : CoordinateRing K :=
  z * conjugate K z

theorem norm_recompose (p q : K[X]) :
    norm K (xClass K p + xClass K q * yClass K) =
      xClass K (p ^ 2 - q ^ 2 * f K) := by
  simp only [norm, map_add, map_mul, conjugate_xClass, conjugate_yClass]
  calc
    (xClass K p + xClass K q * yClass K) *
          (xClass K p + xClass K q * -yClass K) =
        xClass K p ^ 2 - xClass K q ^ 2 * yClass K ^ 2 := by ring
    _ = xClass K p ^ 2 - xClass K q ^ 2 * xClass K (f K) := by
      rw [yClass_sq]
    _ = xClass K (p ^ 2 - q ^ 2 * f K) := by
      change
        AdjoinRoot.of (curvePoly K) p ^ 2 -
            AdjoinRoot.of (curvePoly K) q ^ 2 *
              AdjoinRoot.of (curvePoly K) (f K) =
          AdjoinRoot.of (curvePoly K) (p ^ 2 - q ^ 2 * f K)
      simp only [map_sub, map_mul, map_pow]

end

end MazurProof.N18Mumford
