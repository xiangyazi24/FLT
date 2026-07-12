import FLT.Assumptions.MazurProof.N18RouteC_PhiLocal

set_option maxHeartbeats 0

open scoped NumberField WeierstrassCurve.Affine

namespace MazurProof.N18RouteC.PhiPreimage

open NumberField
open Cyclotomic CyclotomicValuation PhiLocal
open Isogeny IsogenyPoints

noncomputable section

theorem no_square_neg_three (r : L) : r ^ 2 ≠ (-3 : L) := by
  intro hrsq
  have hnorm : (Algebra.norm ℚ r) ^ 2 = (-3 : ℚ) ^ 3 := by
    calc
      (Algebra.norm ℚ r) ^ 2 = Algebra.norm ℚ (r ^ 2) := by rw [map_pow]
      _ = Algebra.norm ℚ (-3 : L) := by rw [hrsq]
      _ = (-3 : ℚ) ^ Module.finrank ℚ L := by
        simpa only [map_neg, map_ofNat] using
          (Algebra.norm_algebraMap (S := L) (-3 : ℚ))
      _ = (-3 : ℚ) ^ 3 := by rw [FieldArithmetic.finrank_L]
  nlinarith [sq_nonneg (Algebra.norm ℚ r)]

theorem cube_injective_L : Function.Injective (fun x : L ↦ x ^ 3) := by
  intro x y hxy
  change x ^ 3 = y ^ 3 at hxy
  by_cases hy : y = 0
  · subst y
    have hx3 : x ^ 3 = 0 := by simpa using hxy
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
  · let u : L := x / y
    have hu : u ^ 3 = 1 := by
      dsimp [u]
      rw [div_pow, hxy]
      field_simp [hy]
    have hfac : (u - 1) * (u ^ 2 + u + 1) = 0 := by
      calc
        (u - 1) * (u ^ 2 + u + 1) = u ^ 3 - 1 := by ring
        _ = 0 := by rw [hu]; ring
    rcases mul_eq_zero.mp hfac with hu1 | hquad
    · have : u = 1 := sub_eq_zero.mp hu1
      dsimp [u] at this
      exact (div_eq_one_iff_eq hy).mp this
    · have hsquare : (2 * u + 1) ^ 2 = (-3 : L) := by
        linear_combination 4 * hquad
      exact (no_square_neg_three (2 * u + 1) hsquare).elim

def preimageD (s : L) : L := 1 - 2 * s
def preimageU (s : L) : L := 2 / preimageD s
def preimageX (s : L) : L := preimageU s + 1
def preimageY (r s : L) : L := preimageU s * r - preimageU s / 2 - 1

theorem preimageD_ne_zero {r s : L}
    (hrel : r ^ 2 + 3 * s ^ 2 = 2 * s * (r ^ 2 - s ^ 2) + 3) :
    preimageD s ≠ 0 := by
  intro hd
  have hs : s = 1 / 2 := by
    unfold preimageD at hd
    linear_combination (-1 / 2 : L) * hd
  rw [hs] at hrel
  have hrel' : r ^ 2 + 3 / 4 = r ^ 2 - 1 / 4 + 3 := by
    convert hrel using 1 <;> norm_num
  have hbad : (3 / 4 : L) = 11 / 4 := by
    calc
      (3 / 4 : L) = (r ^ 2 + 3 / 4) - r ^ 2 := by ring
      _ = (r ^ 2 - 1 / 4 + 3) - r ^ 2 := by rw [hrel']
      _ = 11 / 4 := by ring
  norm_num at hbad

private theorem nonsingular_of_residual_eq_zero
    {W : WeierstrassCurve L} [W.IsElliptic]
    {x y : L} (h : affineResidual W x y = 0) :
    WeierstrassCurve.Affine.Nonsingular W x y := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff']
  simpa [affineResidual] using h

theorem preimage_residual {r s : L}
    (hrel : r ^ 2 + 3 * s ^ 2 = 2 * s * (r ^ 2 - s ^ 2) + 3)
    (hd : preimageD s ≠ 0) :
    affineResidual E0 (preimageX s) (preimageY r s) = 0 := by
  unfold affineResidual E0 preimageX preimageY preimageU
  field_simp [hd]
  unfold preimageD at *
  ring_nf at hrel ⊢
  linear_combination 4 * hrel

theorem preimage_tateU {s : L} (hd : preimageD s ≠ 0) :
    tateU (preimageX s) = preimageU s := by
  unfold tateU preimageX preimageU
  field_simp [hd]
  ring

theorem preimage_phiXi {xi r s : L}
    (hxi : xi = 2 * s * (r ^ 2 - s ^ 2))
    (hrel : r ^ 2 + 3 * s ^ 2 = 2 * s * (r ^ 2 - s ^ 2) + 3)
    (hd : preimageD s ≠ 0) :
    phiXi (preimageX s) = xi := by
  unfold phiXi
  rw [preimage_tateU hd]
  unfold C preimageU
  field_simp [hd]
  unfold preimageD at *
  ring_nf at hxi hrel ⊢
  linear_combination (8 * s - 4) * hxi - 8 * s * hrel

theorem preimage_phiEta {xi eta r s : L}
    (hxi : xi = 2 * s * (r ^ 2 - s ^ 2))
    (hre : dualZ xi eta = r ^ 3 - 9 * r * s ^ 2)
    (hrel : r ^ 2 + 3 * s ^ 2 = 2 * s * (r ^ 2 - s ^ 2) + 3)
    (hd : preimageD s ≠ 0) :
    phiEta (preimageX s) (preimageY r s) = eta := by
  unfold phiEta
  rw [preimage_tateU hd]
  unfold tateW preimageX preimageY preimageU Isogeny.N Isogeny.A Isogeny.B dualZ at *
  field_simp [hd]
  unfold preimageD at *
  ring_nf at hxi hre hrel ⊢
  linear_combination
    (24 * s - 12) * hxi + (16 * s - 8) * hre -
      8 * (r + 3 * s) * hrel

theorem cube_recompose (c : M) :
    let r := realPart c
    let s := imagPart c
    c ^ 3 = embedL (r ^ 3 - 9 * r * s ^ 2) +
      embedL (3 * r ^ 2 * s - 3 * s ^ 3) * qM := by
  dsimp only
  nth_rw 1 [recompose c]
  let r := realPart c
  let s := imagPart c
  have hq3 : qM ^ 3 = -3 * qM := by
    calc
      qM ^ 3 = qM ^ 2 * qM := by ring
      _ = -3 * qM := by rw [qM_sq]
  calc
    (embedL r + embedL s * qM) ^ 3 =
        embedL r ^ 3 + 3 * embedL r ^ 2 * embedL s * qM +
          3 * embedL r * embedL s ^ 2 * qM ^ 2 +
            embedL s ^ 3 * qM ^ 3 := by ring
    _ = embedL (r ^ 3 - 9 * r * s ^ 2) +
        embedL (3 * r ^ 2 * s - 3 * s ^ 3) * qM := by
      rw [qM_sq, hq3]
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
      ring

theorem norm_recompose (c : M) :
    c * NumberField.IsCMField.complexConj M c =
      embedL (realPart c ^ 2 + 3 * imagPart c ^ 2) := by
  nth_rw 1 [recompose c]
  rw [complexConj_recompose]
  calc
    (embedL (realPart c) + embedL (imagPart c) * qM) *
        (embedL (realPart c) - embedL (imagPart c) * qM) =
      embedL (realPart c) ^ 2 - embedL (imagPart c) ^ 2 * qM ^ 2 := by ring
    _ = embedL (realPart c ^ 2 + 3 * imagPart c ^ 2) := by
      rw [qM_sq]
      simp only [map_add, map_mul, map_pow, map_ofNat]
      ring

theorem cube_coordinates
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta)
    {c : M} (hcube : c ^ 3 = phiKappa (.some xi eta h)) :
    let r := realPart c
    let s := imagPart c
    dualZ xi eta = r ^ 3 - 9 * r * s ^ 2 ∧
      xi = 2 * s * (r ^ 2 - s ^ 2) ∧
      dualX xi = r ^ 2 + 3 * s ^ 2 := by
  dsimp only
  let r := realPart c
  let s := imagPart c
  have hcoord :
      embedL (r ^ 3 - 9 * r * s ^ 2) +
          embedL (3 * r ^ 2 * s - 3 * s ^ 3) * qM =
        embedL (dualZ xi eta) + embedL ((3 / 2 : L) * xi) * qM := by
    rw [← cube_recompose c, hcube]
    rfl
  have hreM := congrArg realPart hcoord
  have himM := congrArg imagPart hcoord
  have hre : dualZ xi eta = r ^ 3 - 9 * r * s ^ 2 := by
    simpa only [realPart_embed_add_q] using hreM.symm
  have him : xi = 2 * s * (r ^ 2 - s ^ 2) := by
    have him' : 3 * r ^ 2 * s - 3 * s ^ 3 = (3 / 2 : L) * xi := by
      simpa only [imagPart_embed_add_q] using himM
    calc
      xi = (2 / 3 : L) * ((3 / 2 : L) * xi) := by ring
      _ = (2 / 3 : L) * (3 * r ^ 2 * s - 3 * s ^ 3) := by rw [← him']
      _ = 2 * s * (r ^ 2 - s ^ 2) := by ring
  have hc : c ≠ 0 := by
    intro hc0
    apply phiKappa_ne_zero (.some xi eta h)
    rw [← hcube, hc0]
    norm_num
  have hcC : NumberField.IsCMField.complexConj M c ≠ 0 := by
    simpa only [map_zero] using
      (NumberField.IsCMField.complexConj M).injective.ne_iff.mpr hc
  have hnorm := phiKappa_norm (.some xi eta h)
  rw [← hcube, map_pow, ← mul_pow, norm_recompose] at hnorm
  have hcubeL0 :
      (realPart c ^ 2 + 3 * imagPart c ^ 2) ^ 3 = dualX xi ^ 3 := by
    apply embedL.injective
    have hcoe (x : L) : embedL.toRingHom x = embedL x := rfl
    rw [hcoe, hcoe, map_pow, map_pow]
    simpa only [phiKappaX] using hnorm
  have hcubeL : (r ^ 2 + 3 * s ^ 2) ^ 3 = dualX xi ^ 3 := by
    simpa only [r, s] using hcubeL0
  have hnormL : dualX xi = r ^ 2 + 3 * s ^ 2 :=
    (cube_injective_L hcubeL).symm
  exact ⟨hre, him, hnormL⟩

theorem exists_phi_preimage_of_phiKappa_cube (Q : Ehat0Point)
    (hcube : ∃ c : M, c ^ 3 = phiKappa Q) :
    ∃ P : E0Point, phiPoint P = Q := by
  obtain ⟨c, hc⟩ := hcube
  cases Q with
  | zero => exact ⟨0, phiPoint_zero⟩
  | some xi eta h =>
      let r := realPart c
      let s := imagPart c
      obtain ⟨hre, hxi, hnorm⟩ := cube_coordinates h hc
      have hrel : r ^ 2 + 3 * s ^ 2 =
          2 * s * (r ^ 2 - s ^ 2) + 3 := by
        rw [← hnorm]
        unfold dualX
        rw [hxi]
      have hd : preimageD s ≠ 0 := preimageD_ne_zero hrel
      let x := preimageX s
      let y := preimageY r s
      have hres : affineResidual E0 x y = 0 := preimage_residual hrel hd
      let hP : WeierstrassCurve.Affine.Nonsingular E0 x y :=
        nonsingular_of_residual_eq_zero hres
      have hu : tateU x ≠ 0 := by
        rw [show tateU x = preimageU s by exact preimage_tateU hd]
        unfold preimageU
        exact div_ne_zero (by norm_num) hd
      refine ⟨.some x y hP, ?_⟩
      rw [phiPoint_some_of_tateU_ne_zero hP hu,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨preimage_phiXi hxi hrel hd,
        preimage_phiEta hxi hre hrel hd⟩

theorem phiPoint_surjective : Function.Surjective phiPoint := by
  intro Q
  obtain ⟨c, hc⟩ := phiKappa_is_cube Q
  exact exists_phi_preimage_of_phiKappa_cube Q ⟨c, hc.symm⟩

end

end MazurProof.N18RouteC.PhiPreimage
