import Mathlib
import Mathlib.Order.Northcott
import FLT.EllipticCurve.Torsion
import scratch.A6HeightProto

/-!
# A6 torsion finiteness via projective x-height

Scratch assembly file for replacing the Mordell-Weil finite-generation input in
`MazurProof.rational_torsion_finite_alias`.

This file follows `scratch/A6_R8_Adversarial_FULL.md`: the height lives on primitive
integer representatives of `P¹(ℚ)`, not on raw rational pairs.
-/

open scoped Matrix
open WeierstrassCurve
open WeierstrassCurve.Affine

noncomputable section

set_option maxHeartbeats 2000000

namespace MazurProof

/-- Primitive integral representatives for `P¹(ℚ)`. -/
structure P1Q where
  X : ℤ
  Z : ℤ
  prim : IsCoprime X Z
  not_both_zero : X ≠ 0 ∨ Z ≠ 0

namespace P1Q

/-- Projective equality of two primitive representatives. -/
def Same (x y : P1Q) : Prop :=
  x.X * y.Z = y.X * x.Z

/-- Projective equality between a primitive representative and a raw rational pair. -/
def SameQ (x : P1Q) (A B : ℚ) : Prop :=
  (x.X : ℚ) * B = A * (x.Z : ℚ)

def mulHeight (x : P1Q) : ℕ :=
  max x.X.natAbs x.Z.natAbs

def logHeight (x : P1Q) : ℝ :=
  Real.log (x.mulHeight : ℝ)

def coord (x : P1Q) : ℤ × ℤ :=
  (x.X, x.Z)

lemma one_le_mulHeight (x : P1Q) : 1 ≤ x.mulHeight := by
  rcases x.not_both_zero with hX | hZ
  · have hpos : 0 < x.X.natAbs := Int.natAbs_pos.mpr hX
    exact le_trans hpos (le_max_left _ _)
  · have hpos : 0 < x.Z.natAbs := Int.natAbs_pos.mpr hZ
    exact le_trans hpos (le_max_right _ _)

def infinity : P1Q :=
  { X := 1
    Z := 0
    prim := by simp [isCoprime_zero_right]
    not_both_zero := Or.inl one_ne_zero }

def affine (q : ℚ) : P1Q :=
  { X := q.num
    Z := q.den
    prim := Rat.isCoprime_num_den q
    not_both_zero := Or.inr (by exact_mod_cast q.den_nz) }

private lemma finite_int_natAbs_le (N : ℕ) :
    ({z : ℤ | z.natAbs ≤ N} : Set ℤ).Finite := by
  refine (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  intro z hz
  rw [Set.mem_Icc]
  have hzN : |z| ≤ (N : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hz
  exact abs_le.mp hzN

private lemma finite_box (N : ℕ) :
    ({p : ℤ × ℤ | p.1.natAbs ≤ N ∧ p.2.natAbs ≤ N} : Set (ℤ × ℤ)).Finite := by
  simpa [Set.prod_eq, Set.setOf_and] using
    (finite_int_natAbs_le N).prod (finite_int_natAbs_le N)

theorem mulHeight_northcott_nat (N : ℕ) :
    ({x : P1Q | x.mulHeight ≤ N} : Set P1Q).Finite := by
  let S : Set P1Q := {x | x.mulHeight ≤ N}
  let box : Set (ℤ × ℤ) := {p | p.1.natAbs ≤ N ∧ p.2.natAbs ≤ N}
  have hbox : box.Finite := finite_box N
  have himage : (coord '' S).Finite := by
    refine hbox.subset ?_
    intro p hp
    rcases hp with ⟨x, hx, rfl⟩
    dsimp [box, coord]
    dsimp [S, mulHeight] at hx
    exact ⟨le_trans (le_max_left _ _) hx, le_trans (le_max_right _ _) hx⟩
  exact Set.Finite.of_finite_image himage (by
    intro x _ y _ hxy
    cases x
    cases y
    simp [coord] at hxy
    aesop)

theorem logHeight_northcott : Northcott logHeight where
  finite_le B := by
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp B)
    refine (mulHeight_northcott_nat N).subset ?_
    intro x hx
    dsimp [logHeight] at hx
    have hle_exp : (x.mulHeight : ℝ) ≤ Real.exp B :=
      Real.le_exp_of_log_le hx
    have hlt : (x.mulHeight : ℝ) < (N : ℝ) :=
      lt_of_le_of_lt hle_exp hN
    exact_mod_cast le_of_lt hlt

end P1Q

noncomputable def xRep (E : WeierstrassCurve ℚ) : (E⁄ℚ).Point → P1Q
  | 0 => P1Q.infinity
  | Point.some x _ _ => P1Q.affine x

noncomputable def xHeight (E : WeierstrassCurve ℚ) (P : (E⁄ℚ).Point) : ℝ :=
  P1Q.logHeight (xRep E P)

private lemma point_xRep_eq_of_xRep_eq
    (E : WeierstrassCurve ℚ) {P Q : (E⁄ℚ).Point}
    (h : xRep E P = xRep E Q) :
    P.xRep = Q.xRep := by
  rcases P with _ | ⟨xP, yP, hP⟩
  · rcases Q with _ | ⟨xQ, yQ, hQ⟩
    · simp
    · exfalso
      have hz := congrArg P1Q.Z h
      have hz' : (0 : ℤ) = xQ.den := by
        simpa [xRep, P1Q.infinity, P1Q.affine] using hz
      have hden : (xQ.den : ℤ) ≠ 0 := by exact_mod_cast xQ.den_nz
      exact hden hz'.symm
  · rcases Q with _ | ⟨xQ, yQ, hQ⟩
    · exfalso
      have hz := congrArg P1Q.Z h
      simp [xRep, P1Q.infinity, P1Q.affine] at hz
    · have hxnum := congrArg P1Q.X h
      have hxden := congrArg P1Q.Z h
      simp [xRep, P1Q.affine] at hxnum hxden
      have hx : xP = xQ := Rat.ext hxnum hxden
      ext i
      fin_cases i <;> simp [Point.xRep_some, hx]

theorem xRep_finite_fibers
    (E : WeierstrassCurve ℚ) (x : P1Q) :
    ({P : (E⁄ℚ).Point | xRep E P = x} : Set (E⁄ℚ).Point).Finite := by
  classical
  by_cases hnonempty : ∃ P : (E⁄ℚ).Point, xRep E P = x
  · rcases hnonempty with ⟨P0, hP0⟩
    have hfin : ({P0, -P0} : Set (E⁄ℚ).Point).Finite := by
      exact (Set.finite_singleton (-P0)).insert P0
    refine hfin.subset ?_
    intro P hP
    have hsame : xRep E P = xRep E P0 := hP.trans hP0.symm
    have hxraw : P.xRep = P0.xRep := point_xRep_eq_of_xRep_eq E hsame
    have h_or := (Point.xRep_eq_xRep_iff (W := E⁄ℚ) (P := P) (Q := P0)).mp hxraw
    rcases h_or with rfl | hneg
    · simp
    · simp [hneg]
  · have hempty : ({P : (E⁄ℚ).Point | xRep E P = x} : Set (E⁄ℚ).Point) = ∅ := by
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hP
      exact hnonempty ⟨P, hP⟩
    rw [hempty]
    exact Set.finite_empty

theorem xHeight_northcott (E : WeierstrassCurve ℚ) :
    Northcott (xHeight E) := by
  haveI : Northcott P1Q.logHeight := P1Q.logHeight_northcott
  change Northcott (P1Q.logHeight ∘ xRep E)
  exact Northcott.comp_of_finite_fibers
    (h := xRep E) (h' := P1Q.logHeight)
    (by
      intro y
      simpa [Set.preimage] using xRep_finite_fibers E y)

open WeierstrassCurve.HeightDoubling

private def SameP1 (u v : Fin 2 → ℚ) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ v = c • u

namespace SameP1

private lemma mk_vec
    {u v : Fin 2 → ℚ} {c : ℚ}
    (hc : c ≠ 0)
    (h0 : v 0 = c * u 0)
    (h1 : v 1 = c * u 1) :
    SameP1 u v := by
  refine ⟨c, hc, ?_⟩
  ext i
  fin_cases i
  · simpa [Pi.smul_apply] using h0
  · simpa [Pi.smul_apply] using h1

private lemma smul_right {u v : Fin 2 → ℚ} (h : SameP1 u v) {c : ℚ} (hc : c ≠ 0) :
    SameP1 u (c • v) := by
  rcases h with ⟨a, ha, rfl⟩
  refine ⟨c * a, mul_ne_zero hc ha, ?_⟩
  ext i
  simp [Pi.smul_apply, mul_assoc]

end SameP1

private lemma dupNumH_scale
    (E : WeierstrassCurve ℚ) (c X Z : ℚ) :
    dupNumH E (c * X) (c * Z) = c ^ 4 * dupNumH E X Z := by
  simp [dupNumH]
  ring

private lemma dupDenH_scale
    (E : WeierstrassCurve ℚ) (c X Z : ℚ) :
    dupDenH E (c * X) (c * Z) = c ^ 4 * dupDenH E X Z := by
  simp [dupDenH]
  ring

private lemma rat_num_eq_self_mul_den (q : ℚ) :
    (q.num : ℚ) = q * (q.den : ℚ) := by
  have hden : ((q.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  calc
    (q.num : ℚ) = ((q.num : ℚ) / (q.den : ℚ)) * (q.den : ℚ) := by
      field_simp [hden]
    _ = q * (q.den : ℚ) := by
      rw [Rat.num_div_den]

private lemma p1q_sameQ_of_sameP1_xRep
    (E : WeierstrassCurve ℚ) {Q : (E⁄ℚ).Point} {A B : ℚ}
    (h : SameP1 Q.xRep ![A, B]) :
    P1Q.SameQ (xRep E Q) A B := by
  rcases h with ⟨c, hc, hv⟩
  rcases Q with _ | ⟨x, y, hQ⟩
  · have hB : B = 0 := by
      have h1 := congrFun hv 1
      simpa [Affine.Point.xRep, Pi.smul_apply] using h1
    simp [P1Q.SameQ, xRep, P1Q.infinity, hB]
  · have hA : A = c * x := by
      have h0 := congrFun hv 0
      simpa [Pi.smul_apply] using h0
    have hB : B = c := by
      have h1 := congrFun hv 1
      simpa [Pi.smul_apply] using h1
    simp only [P1Q.SameQ, xRep, P1Q.affine]
    rw [hA, hB]
    have hden_cast : (x.den : ℚ) = (((x.den : ℤ) : ℚ)) := by norm_num
    have hxnum : (x.num : ℚ) = x * (((x.den : ℤ) : ℚ)) := by
      rw [rat_num_eq_self_mul_den, hden_cast]
    rw [hxnum]
    ring

private lemma dupDenH_eq_Yder_sq
    (W : WeierstrassCurve ℚ)
    {x y : ℚ} (hE : Affine.Equation W x y) :
    dupDenH W x 1 = (y - Affine.negY W x y) ^ 2 := by
  have hE0 : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  rw [dupDenH, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, Affine.negY]
  linear_combination (norm := ring1) -4 * hE0

private lemma dupNumH_eq_polynomialX_sq_of_Yder_zero
    (W : WeierstrassCurve ℚ)
    {x y : ℚ} (hE : Affine.Equation W x y)
    (hY : y - Affine.negY W x y = 0) :
    dupNumH W x 1 =
      (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) ^ 2 := by
  have hE0 : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  have hY0 : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    rw [Affine.negY] at hY
    linear_combination (norm := ring1) hY
  rw [dupNumH, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination (norm := ring1)
      (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) * hE0
    + (-(W.a₁ ^ 2) * y + W.a₁ * W.a₂ * x + W.a₁ * W.a₄
        + W.a₁ * x ^ 2 - W.a₂ * W.a₃ - 2 * W.a₂ * y
        - 2 * W.a₃ * x - 4 * x * y) * hY0

private lemma dupNumH_eq_dupDenH_mul_addX_of_Yder_ne
    (W : WeierstrassCurve ℚ)
    {x y : ℚ} (hE : Affine.Equation W x y)
    (hy : y ≠ Affine.negY W x y) :
    dupNumH W x 1 =
      dupDenH W x 1 * Affine.addX W x x (Affine.slope W x x y y) := by
  have hE0 : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  have hden : y - Affine.negY W x y ≠ 0 := sub_ne_zero.mpr hy
  rw [dupNumH, dupDenH, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, Affine.addX]
  rw [Affine.slope_of_Y_ne (W := W) rfl hy]
  field_simp [hden]
  rw [Affine.negY]
  linear_combination (norm := ring1)
    (W.a₁ ^ 2 * x + W.a₁ * W.a₃ + 4 * W.a₂ * x
      + 2 * W.a₄ + 6 * x ^ 2) ^ 2 * hE0

private lemma dupNumH_ne_zero_of_Yder_zero
    (W : WeierstrassCurve ℚ)
    {x y : ℚ} (h : Affine.Nonsingular W x y)
    (hY : y - Affine.negY W x y = 0) :
    dupNumH W x 1 ≠ 0 := by
  have hYpoly : (Affine.polynomialY W).evalEval x y = 0 := by
    rw [Affine.evalEval_polynomialY]
    rw [Affine.negY] at hY
    linear_combination (norm := ring1) hY
  have hXpoly : (Affine.polynomialX W).evalEval x y ≠ 0 :=
    h.2.resolve_right (by simpa [hYpoly])
  have hX :
      W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 := by
    simpa [Affine.evalEval_polynomialX] using hXpoly
  have hN := dupNumH_eq_polynomialX_sq_of_Yder_zero (W := W) h.1 hY
  rw [hN]
  exact pow_ne_zero 2 hX

private theorem xRep_two_nsmul_same_dup_affine
    (W : WeierstrassCurve ℚ)
    (P : Affine.Point W) :
    SameP1 ((2 • P).xRep)
      ![dupNumH W (P.xRep 0) (P.xRep 1),
        dupDenH W (P.xRep 0) (P.xRep 1)] := by
  classical
  rcases P with _ | ⟨x, y, h⟩
  · refine SameP1.mk_vec
      (u := ((2 • (0 : Affine.Point W)).xRep))
      (v := ![dupNumH W ((0 : Affine.Point W).xRep 0) ((0 : Affine.Point W).xRep 1),
        dupDenH W ((0 : Affine.Point W).xRep 0) ((0 : Affine.Point W).xRep 1)])
      (c := 1) one_ne_zero ?_ ?_
    · simp [dupNumH]
    · simp [dupDenH]
  · by_cases hy : y = Affine.negY W x y
    · have hY : y - Affine.negY W x y = 0 := sub_eq_zero.mpr hy
      have htwo :
          2 • (Point.some x y h : Affine.Point W) = 0 := by
        simpa [two_nsmul] using
          (Point.add_self_of_Y_eq (W := W) (h₁ := h) hy)
      have hD0 : dupDenH W x 1 = 0 := by
        rw [dupDenH_eq_Yder_sq (W := W) h.1, hY]
        norm_num
      have hN0 : dupNumH W x 1 ≠ 0 :=
        dupNumH_ne_zero_of_Yder_zero (W := W) h hY
      refine SameP1.mk_vec
        (u := ((2 • (Point.some x y h : Affine.Point W)).xRep))
        (v := ![dupNumH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1),
          dupDenH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1)])
        (c := dupNumH W x 1) hN0 ?_ ?_
      · simp [htwo]
      · simp [htwo, hD0]
    · have hYne : y - Affine.negY W x y ≠ 0 := sub_ne_zero.mpr hy
      have hD_eq : dupDenH W x 1 = (y - Affine.negY W x y) ^ 2 :=
        dupDenH_eq_Yder_sq (W := W) h.1
      have hDne : dupDenH W x 1 ≠ 0 := by
        rw [hD_eq]
        exact pow_ne_zero 2 hYne
      have htwo :
          2 • (Point.some x y h : Affine.Point W) =
            Point.some _ _ (Affine.nonsingular_add h h (fun hxy => hy hxy.right)) := by
        simpa [two_nsmul] using
          (Point.add_self_of_Y_ne (W := W) (h₁ := h) hy)
      have hN :
          dupNumH W x 1 =
            dupDenH W x 1 * Affine.addX W x x (Affine.slope W x x y y) :=
        dupNumH_eq_dupDenH_mul_addX_of_Yder_ne (W := W) h.1 hy
      refine SameP1.mk_vec
        (u := ((2 • (Point.some x y h : Affine.Point W)).xRep))
        (v := ![dupNumH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1),
          dupDenH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1)])
        (c := dupDenH W x 1) hDne ?_ ?_
      · simp [htwo, hN]
      · simp [htwo]

/--
Projective duplication formula, stated against the primitive `P1Q` x-representative.

This is the isolated EC group-law seam from audit §2.A/§5.2.  It should be closed by adapting
the `SameP1` proof in `scratch/A6_R5_EC_Duplication_FULL.md` and then using degree-4
homogeneity to pass from the raw point vector `[x:1]` to the primitive integer rep `[num:den]`.
-/
theorem xRep_two_nsmul_same_dup
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) :
    P1Q.SameQ (xRep E (2 • P))
      (dupNumH E ((xRep E P).X : ℚ) ((xRep E P).Z : ℚ))
      (dupDenH E ((xRep E P).X : ℚ) ((xRep E P).Z : ℚ)) := by
  rcases P with _ | ⟨x, y, hP⟩
  · have htwo : 2 • (Point.zero : (E⁄ℚ).Point) = Point.zero := by
      change 2 • (0 : (E⁄ℚ).Point) = (0 : (E⁄ℚ).Point)
      simp
    rw [htwo]
    simp [P1Q.SameQ, xRep, P1Q.infinity, dupNumH, dupDenH]
  · let d : ℚ := (x.den : ℚ)
    have hd : d ≠ 0 := by
      dsimp [d]
      exact_mod_cast x.den_nz
    have hraw :
        SameP1 ((2 • (Point.some x y hP : (E⁄ℚ).Point)).xRep)
          ![dupNumH E x 1, dupDenH E x 1] := by
      simpa [dupNumH, dupDenH, WeierstrassCurve.baseChange] using
        xRep_two_nsmul_same_dup_affine (W := E⁄ℚ) (Point.some x y hP)
    have hX : ((P1Q.affine x).X : ℚ) = d * x := by
      dsimp [P1Q.affine, d]
      rw [rat_num_eq_self_mul_den]
      ring
    have hZ : ((P1Q.affine x).Z : ℚ) = d * 1 := by
      dsimp [P1Q.affine, d]
      norm_num
    have hscale :
        ![dupNumH E ((P1Q.affine x).X : ℚ) ((P1Q.affine x).Z : ℚ),
          dupDenH E ((P1Q.affine x).X : ℚ) ((P1Q.affine x).Z : ℚ)]
          =
        d ^ 4 • ![dupNumH E x 1, dupDenH E x 1] := by
      ext i <;> fin_cases i
      · rw [hX, hZ, dupNumH_scale]
        simp
      · rw [hX, hZ, dupDenH_scale]
        simp
    have hprim :
        SameP1 ((2 • (Point.some x y hP : (E⁄ℚ).Point)).xRep)
          ![dupNumH E ((P1Q.affine x).X : ℚ) ((P1Q.affine x).Z : ℚ),
            dupDenH E ((P1Q.affine x).X : ℚ) ((P1Q.affine x).Z : ℚ)] := by
      rw [hscale]
      exact SameP1.smul_right hraw (pow_ne_zero 4 hd)
    exact p1q_sameQ_of_sameP1_xRep E hprim

private structure HomogeneousBezoutCertificate where
  F : ℤ → ℤ → ℤ
  G : ℤ → ℤ → ℤ
  D : ℤ
  Ux : ℤ → ℤ → ℤ
  Vx : ℤ → ℤ → ℤ
  Uz : ℤ → ℤ → ℤ
  Vz : ℤ → ℤ → ℤ
  bezoutX : ∀ X Z : ℤ,
    D * X ^ 7 = Ux X Z * F X Z + Vx X Z * G X Z
  bezoutZ : ∀ X Z : ℤ,
    D * Z ^ 7 = Uz X Z * F X Z + Vz X Z * G X Z

namespace HomogeneousBezoutCertificate

private lemma dvd_natAbs_add_mul_of_dvd_natAbs
    {d : ℕ} {a b u v : ℤ}
    (ha : d ∣ a.natAbs) (hb : d ∣ b.natAbs) :
    d ∣ (u * a + v * b).natAbs := by
  have haZ : (d : ℤ) ∣ a := by
    exact Int.natCast_dvd.mpr ha
  have hbZ : (d : ℤ) ∣ b := by
    exact Int.natCast_dvd.mpr hb
  have hlinZ : (d : ℤ) ∣ u * a + v * b := by
    exact dvd_add (dvd_mul_of_dvd_right haZ u) (dvd_mul_of_dvd_right hbZ v)
  exact Int.natCast_dvd.mp hlinZ

private theorem gcd_dvd_D_natAbs_of_natAbs_coprime
    (C : HomogeneousBezoutCertificate)
    {X Z : ℤ}
    (hcop : Nat.Coprime X.natAbs Z.natAbs) :
    Nat.gcd (C.F X Z).natAbs (C.G X Z).natAbs ∣ C.D.natAbs := by
  let d : ℕ := Nat.gcd (C.F X Z).natAbs (C.G X Z).natAbs
  have hdF : d ∣ (C.F X Z).natAbs := Nat.gcd_dvd_left _ _
  have hdG : d ∣ (C.G X Z).natAbs := Nat.gcd_dvd_right _ _
  have hd_comboX :
      d ∣ (C.Ux X Z * C.F X Z + C.Vx X Z * C.G X Z).natAbs :=
    dvd_natAbs_add_mul_of_dvd_natAbs hdF hdG
  have hd_comboZ :
      d ∣ (C.Uz X Z * C.F X Z + C.Vz X Z * C.G X Z).natAbs :=
    dvd_natAbs_add_mul_of_dvd_natAbs hdF hdG
  have hd_DX : d ∣ (C.D * X ^ 7).natAbs := by
    simpa [C.bezoutX X Z] using hd_comboX
  have hd_DZ : d ∣ (C.D * Z ^ 7).natAbs := by
    simpa [C.bezoutZ X Z] using hd_comboZ
  have hd_DX' : d ∣ C.D.natAbs * X.natAbs ^ 7 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hd_DX
  have hd_DZ' : d ∣ C.D.natAbs * Z.natAbs ^ 7 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hd_DZ
  have hpowcop : Nat.Coprime (X.natAbs ^ 7) (Z.natAbs ^ 7) := by
    exact hcop.pow 7 7
  have hd_gcd :
      d ∣ Nat.gcd (C.D.natAbs * X.natAbs ^ 7)
                   (C.D.natAbs * Z.natAbs ^ 7) :=
    Nat.dvd_gcd hd_DX' hd_DZ'
  have hgcd_eval :
      Nat.gcd (C.D.natAbs * X.natAbs ^ 7)
                   (C.D.natAbs * Z.natAbs ^ 7) = C.D.natAbs := by
    calc
      Nat.gcd (C.D.natAbs * X.natAbs ^ 7)
          (C.D.natAbs * Z.natAbs ^ 7)
          = C.D.natAbs * Nat.gcd (X.natAbs ^ 7) (Z.natAbs ^ 7) := by
            exact Nat.gcd_mul_left (C.D.natAbs) (X.natAbs ^ 7) (Z.natAbs ^ 7)
      _ = C.D.natAbs := by
        rw [hpowcop.gcd_eq_one]
        simp
  simpa [hgcd_eval] using hd_gcd

end HomogeneousBezoutCertificate

private def dupBezoutUZ (E : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  E.Δ * ((E.b₂ ^ 2 - 32 * E.b₄) * Z ^ 3
    - 8 * E.b₂ * X * Z ^ 2 - 48 * X ^ 2 * Z)

private def dupBezoutVZ (E : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  E.Δ * ((E.b₂ * E.b₄ - 27 * E.b₆) * Z ^ 3
    - 10 * E.b₄ * X * Z ^ 2 - E.b₂ * X ^ 2 * Z + 12 * X ^ 3)

private def dupBezoutUX (E : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  let A := E.b₂ ^ 2 * E.b₄ * E.b₆ - E.b₂ * E.b₄ ^ 3
    - 5 * E.b₂ * E.b₆ ^ 2 + E.b₄ ^ 2 * E.b₆
  let B := E.b₂ ^ 2 * E.b₆ ^ 2 - 13 * E.b₂ * E.b₄ ^ 2 * E.b₆
    + 12 * E.b₄ ^ 4 + 44 * E.b₄ * E.b₆ ^ 2
  let C := E.b₂ * E.b₄ * E.b₆ - E.b₄ ^ 3 - 4 * E.b₆ ^ 2
  E.Δ ^ 2 * X ^ 3 + A * E.Δ * Z * X ^ 2
    - (B * E.Δ / 4) * Z ^ 2 * X + ((3 / 2 : ℚ) * E.b₆ * C * E.Δ) * Z ^ 3

private def dupBezoutVX (E : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  let A := E.b₂ ^ 2 * E.b₄ * E.b₆ - E.b₂ * E.b₄ ^ 3
    - 5 * E.b₂ * E.b₆ ^ 2 + E.b₄ ^ 2 * E.b₆
  let C := E.b₂ * E.b₄ * E.b₆ - E.b₄ ^ 3 - 4 * E.b₆ ^ 2
  let D := E.b₂ ^ 2 * E.b₆ ^ 2 - 6 * E.b₂ * E.b₄ ^ 2 * E.b₆
    + 5 * E.b₄ ^ 4 + 16 * E.b₄ * E.b₆ ^ 2
  let fcoef := E.b₂ ^ 3 * E.b₆ ^ 2 - 2 * E.b₂ ^ 2 * E.b₄ ^ 2 * E.b₆
    + E.b₂ * E.b₄ ^ 4 - 52 * E.b₂ * E.b₄ * E.b₆ ^ 2
    + 52 * E.b₄ ^ 3 * E.b₆ + 192 * E.b₆ ^ 3
  0 - (A * E.Δ / 4) * X ^ 3 - (D * E.Δ / 4) * Z * X ^ 2
    - (fcoef * E.Δ / 16) * Z ^ 2 * X
    + ((3 / 8 : ℚ) * (E.b₂ * E.b₆ - E.b₄ ^ 2) * C * E.Δ) * Z ^ 3

private lemma b₈_eq_of_b_relation (E : WeierstrassCurve ℚ) :
    E.b₈ = (E.b₂ * E.b₆ - E.b₄ ^ 2) / 4 := by
  have hrel : E.b₂ * E.b₆ - E.b₄ ^ 2 - 4 * E.b₈ = 0 := by
    rw [← E.b_relation]
    ring
  linear_combination (norm := ring1) (-1 / 4 : ℚ) * hrel

private lemma dup_bezoutZ_Q
    (E : WeierstrassCurve ℚ) (X Z : ℚ) :
    E.Δ ^ 2 * Z ^ 7 =
      dupBezoutUZ E X Z * dupNumH E X Z + dupBezoutVZ E X Z * dupDenH E X Z := by
  simp [dupBezoutUZ, dupBezoutVZ, dupNumH, dupDenH, WeierstrassCurve.Δ,
    b₈_eq_of_b_relation]
  ring

private lemma dup_bezoutX_Q
    (E : WeierstrassCurve ℚ) (X Z : ℚ) :
    E.Δ ^ 2 * X ^ 7 =
      dupBezoutUX E X Z * dupNumH E X Z + dupBezoutVX E X Z * dupDenH E X Z := by
  simp [dupBezoutUX, dupBezoutVX, dupNumH, dupDenH, WeierstrassCurve.Δ,
    b₈_eq_of_b_relation]
  ring_nf

private def IsRatInt (q : ℚ) : Prop :=
  ∃ z : ℤ, q = z

namespace IsRatInt

private lemma add {a b : ℚ} (ha : IsRatInt a) (hb : IsRatInt b) :
    IsRatInt (a + b) := by
  rcases ha with ⟨m, rfl⟩
  rcases hb with ⟨n, rfl⟩
  exact ⟨m + n, by norm_num⟩

private lemma neg {a : ℚ} (ha : IsRatInt a) :
    IsRatInt (-a) := by
  rcases ha with ⟨m, rfl⟩
  exact ⟨-m, by norm_num⟩

private lemma sub {a b : ℚ} (ha : IsRatInt a) (hb : IsRatInt b) :
    IsRatInt (a - b) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg

private lemma den_eq_one {q : ℚ} (hq : IsRatInt q) :
    q.den = 1 := by
  rcases hq with ⟨z, rfl⟩
  simp

private lemma of_eq {a b : ℚ} (ha : IsRatInt a) (h : a = b) :
    IsRatInt b := by
  rw [← h]
  exact ha

end IsRatInt

private def denProd (qs : List ℚ) : ℕ :=
  qs.foldr (fun q n => q.den * n) 1

private lemma den_dvd_denProd_of_mem {q : ℚ} {qs : List ℚ} (h : q ∈ qs) :
    q.den ∣ denProd qs := by
  induction qs with
  | nil => simp at h
  | cons r rs ih =>
      simp [denProd] at h ⊢
      rcases h with hqr | hmem
      · subst q
        exact Nat.dvd_mul_right r.den (denProd rs)
      · exact dvd_mul_of_dvd_right (ih hmem) r.den

private lemma denProd_pos (qs : List ℚ) :
    0 < denProd qs := by
  induction qs with
  | nil => simp [denProd]
  | cons q qs ih =>
      change 0 < q.den * denProd qs
      exact Nat.mul_pos q.den_pos ih

private lemma isRatInt_nat_mul_of_den_dvd {L : ℕ} {q : ℚ} (h : q.den ∣ L) :
    IsRatInt ((L : ℚ) * q) := by
  rcases h with ⟨k, hk⟩
  refine ⟨q.num * (k : ℤ), ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  calc
    (L : ℚ) * q = ((q.den * k : ℕ) : ℚ) * q := by rw [← hk]
    _ = ((q.den * k : ℕ) : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) := by
      rw [Rat.num_div_den]
    _ = ((q.num * (k : ℤ) : ℤ) : ℚ) := by
      field_simp [hden]
      norm_num
      ring

private lemma isRatInt_nat_mul_coeff_monomial {L : ℕ} (X Z : ℤ) {c : ℚ}
    (hc : c.den ∣ L) (a b : ℕ) :
    IsRatInt ((L : ℚ) * (c * (X : ℚ) ^ a * (Z : ℚ) ^ b)) := by
  obtain ⟨m, hm⟩ := isRatInt_nat_mul_of_den_dvd (L := L) hc
  refine ⟨m * X ^ a * Z ^ b, ?_⟩
  calc
    (L : ℚ) * (c * (X : ℚ) ^ a * (Z : ℚ) ^ b) =
        ((L : ℚ) * c) * (X : ℚ) ^ a * (Z : ℚ) ^ b := by ring
    _ = (m * X ^ a * Z ^ b : ℤ) := by
      rw [hm]
      norm_num

private def dupUXA (E : WeierstrassCurve ℚ) : ℚ :=
  E.b₂ ^ 2 * E.b₄ * E.b₆ - E.b₂ * E.b₄ ^ 3
    - 5 * E.b₂ * E.b₆ ^ 2 + E.b₄ ^ 2 * E.b₆

private def dupUXB (E : WeierstrassCurve ℚ) : ℚ :=
  E.b₂ ^ 2 * E.b₆ ^ 2 - 13 * E.b₂ * E.b₄ ^ 2 * E.b₆
    + 12 * E.b₄ ^ 4 + 44 * E.b₄ * E.b₆ ^ 2

private def dupUXC (E : WeierstrassCurve ℚ) : ℚ :=
  E.b₂ * E.b₄ * E.b₆ - E.b₄ ^ 3 - 4 * E.b₆ ^ 2

private def dupVXD (E : WeierstrassCurve ℚ) : ℚ :=
  E.b₂ ^ 2 * E.b₆ ^ 2 - 6 * E.b₂ * E.b₄ ^ 2 * E.b₆
    + 5 * E.b₄ ^ 4 + 16 * E.b₄ * E.b₆ ^ 2

private def dupVXf (E : WeierstrassCurve ℚ) : ℚ :=
  E.b₂ ^ 3 * E.b₆ ^ 2 - 2 * E.b₂ ^ 2 * E.b₄ ^ 2 * E.b₆
    + E.b₂ * E.b₄ ^ 4 - 52 * E.b₂ * E.b₄ * E.b₆ ^ 2
    + 52 * E.b₄ ^ 3 * E.b₆ + 192 * E.b₆ ^ 3

private def cUZ0 (E : WeierstrassCurve ℚ) : ℚ :=
  E.Δ * (E.b₂ ^ 2 - 32 * E.b₄)

private def cUZ1 (E : WeierstrassCurve ℚ) : ℚ :=
  -8 * E.Δ * E.b₂

private def cUZ2 (E : WeierstrassCurve ℚ) : ℚ :=
  -48 * E.Δ

private def cVZ0 (E : WeierstrassCurve ℚ) : ℚ :=
  E.Δ * (E.b₂ * E.b₄ - 27 * E.b₆)

private def cVZ1 (E : WeierstrassCurve ℚ) : ℚ :=
  -10 * E.Δ * E.b₄

private def cVZ2 (E : WeierstrassCurve ℚ) : ℚ :=
  -E.Δ * E.b₂

private def cVZ3 (E : WeierstrassCurve ℚ) : ℚ :=
  12 * E.Δ

private def cUX0 (E : WeierstrassCurve ℚ) : ℚ :=
  (3 / 2 : ℚ) * E.b₆ * dupUXC E * E.Δ

private def cUX1 (E : WeierstrassCurve ℚ) : ℚ :=
  -(dupUXB E * E.Δ / 4)

private def cUX2 (E : WeierstrassCurve ℚ) : ℚ :=
  dupUXA E * E.Δ

private def cUX3 (E : WeierstrassCurve ℚ) : ℚ :=
  E.Δ ^ 2

private def cVX0 (E : WeierstrassCurve ℚ) : ℚ :=
  (3 / 8 : ℚ) * (E.b₂ * E.b₆ - E.b₄ ^ 2) * dupUXC E * E.Δ

private def cVX1 (E : WeierstrassCurve ℚ) : ℚ :=
  -(dupVXf E * E.Δ / 16)

private def cVX2 (E : WeierstrassCurve ℚ) : ℚ :=
  -(dupVXD E * E.Δ / 4)

private def cVX3 (E : WeierstrassCurve ℚ) : ℚ :=
  -(dupUXA E * E.Δ / 4)

private def dupClearCoeffs (E : WeierstrassCurve ℚ) : List ℚ :=
  [1, -E.b₄, -(2 * E.b₆), -E.b₈, 4, E.b₂, 2 * E.b₄, E.b₆,
    E.Δ ^ 2,
    cUZ0 E, cUZ1 E, cUZ2 E,
    cVZ0 E, cVZ1 E, cVZ2 E, cVZ3 E,
    cUX0 E, cUX1 E, cUX2 E, cUX3 E,
    cVX0 E, cVX1 E, cVX2 E, cVX3 E]

@[irreducible] private def dupClearDen (E : WeierstrassCurve ℚ) : ℕ :=
  denProd (dupClearCoeffs E)

private lemma dupClearDen_pos (E : WeierstrassCurve ℚ) :
    0 < dupClearDen E := by
  rw [dupClearDen]
  exact denProd_pos _

private lemma dupCoeff_dvd_clearDen {E : WeierstrassCurve ℚ} {c : ℚ}
    (h : c ∈ dupClearCoeffs E) :
    c.den ∣ dupClearDen E := by
  rw [dupClearDen]
  exact den_dvd_denProd_of_mem h

private lemma dupCoeff_clear_isRatInt {E : WeierstrassCurve ℚ} (X Z : ℤ)
    {c : ℚ} (h : c ∈ dupClearCoeffs E) (a b : ℕ) :
    IsRatInt ((dupClearDen E : ℚ) * (c * (X : ℚ) ^ a * (Z : ℚ) ^ b)) :=
  isRatInt_nat_mul_coeff_monomial (L := dupClearDen E) X Z
    (dupCoeff_dvd_clearDen h) a b

private lemma dupNumH_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupNumH E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := (1 : ℚ))
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 4 0
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := -E.b₄)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 2
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := -(2 * E.b₆))
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 3
  have h4 := dupCoeff_clear_isRatInt (E := E) X Z (c := -E.b₈)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 4
  refine IsRatInt.of_eq (((h1.add h2).add h3).add h4) ?_
  simp [dupNumH]
  ring

private lemma dupDenH_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupDenH E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := (4 : ℚ))
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 3 1
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := E.b₂)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 2
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := 2 * E.b₄)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 3
  have h4 := dupCoeff_clear_isRatInt (E := E) X Z (c := E.b₆)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 4
  refine IsRatInt.of_eq (((h1.add h2).add h3).add h4) ?_
  simp [dupDenH]
  ring

private lemma dupBezoutUZ_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupBezoutUZ E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUZ0 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 3
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUZ1 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 2
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUZ2 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 1
  refine IsRatInt.of_eq ((h1.add h2).add h3) ?_
  simp [dupBezoutUZ, cUZ0, cUZ1, cUZ2]
  ring

private lemma dupBezoutVZ_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupBezoutVZ E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVZ0 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 3
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVZ1 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 2
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVZ2 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 1
  have h4 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVZ3 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 3 0
  refine IsRatInt.of_eq (((h1.add h2).add h3).add h4) ?_
  simp [dupBezoutVZ, cVZ0, cVZ1, cVZ2, cVZ3]
  ring

private lemma dupBezoutUX_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupBezoutUX E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUX3 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 3 0
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUX2 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 1
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUX1 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 2
  have h4 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUX0 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 3
  refine IsRatInt.of_eq (((h1.add h2).add h3).add h4) ?_
  simp [dupBezoutUX, cUX0, cUX1, cUX2, cUX3, dupUXA, dupUXB, dupUXC]
  ring

private lemma dupBezoutVX_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupBezoutVX E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVX3 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 3 0
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVX2 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 1
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVX1 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 2
  have h4 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVX0 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 3
  refine IsRatInt.of_eq (((h1.add h2).add h3).add h4) ?_
  simp [dupBezoutVX, cVX0, cVX1, cVX2, cVX3, dupUXA, dupUXC, dupVXD, dupVXf]
  ring

private lemma deltaSq_clear_isRatInt (E : WeierstrassCurve ℚ) :
    IsRatInt (((dupClearDen E : ℚ) ^ 2) * E.Δ ^ 2) := by
  have hbase : IsRatInt ((dupClearDen E : ℚ) * (E.Δ ^ 2)) :=
    isRatInt_nat_mul_of_den_dvd (L := dupClearDen E)
      (q := E.Δ ^ 2)
      (dupCoeff_dvd_clearDen (E := E) (c := E.Δ ^ 2) (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]))
  obtain ⟨m, hm⟩ := hbase
  refine ⟨(dupClearDen E : ℤ) * m, ?_⟩
  calc
    ((dupClearDen E : ℚ) ^ 2) * E.Δ ^ 2 =
        (dupClearDen E : ℚ) * ((dupClearDen E : ℚ) * E.Δ ^ 2) := by ring_nf
    _ = (((dupClearDen E : ℤ) * m : ℤ) : ℚ) := by
      rw [hm]
      norm_cast

private def clearRatInt (q : ℚ) : ℤ :=
  q.num

private lemma clearRatInt_spec {q : ℚ} (hq : IsRatInt q) :
    (clearRatInt q : ℚ) = q := by
  exact Rat.coe_int_num_of_den_eq_one (IsRatInt.den_eq_one hq)

private def dupFZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupNumH E (X : ℚ) (Z : ℚ))

private def dupGZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupDenH E (X : ℚ) (Z : ℚ))

private def dupUXZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupBezoutUX E (X : ℚ) (Z : ℚ))

private def dupVXZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupBezoutVX E (X : ℚ) (Z : ℚ))

private def dupUZZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupBezoutUZ E (X : ℚ) (Z : ℚ))

private def dupVZZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupBezoutVZ E (X : ℚ) (Z : ℚ))

private def dupDZ (E : WeierstrassCurve ℚ) : ℤ :=
  clearRatInt (((dupClearDen E : ℚ) ^ 2) * E.Δ ^ 2)

private lemma dupFZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupFZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupNumH E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupNumH_clear_isRatInt E X Z)

private lemma dupGZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupGZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupDenH E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupDenH_clear_isRatInt E X Z)

private lemma dupUXZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupUXZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupBezoutUX E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupBezoutUX_clear_isRatInt E X Z)

private lemma dupVXZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupVXZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupBezoutVX E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupBezoutVX_clear_isRatInt E X Z)

private lemma dupUZZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupUZZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupBezoutUZ E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupBezoutUZ_clear_isRatInt E X Z)

private lemma dupVZZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupVZZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupBezoutVZ E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupBezoutVZ_clear_isRatInt E X Z)

private lemma dupDZ_spec (E : WeierstrassCurve ℚ) :
    (dupDZ E : ℚ) = ((dupClearDen E : ℚ) ^ 2) * E.Δ ^ 2 := by
  exact clearRatInt_spec (deltaSq_clear_isRatInt E)

private lemma dup_bezoutX_Z
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    dupDZ E * X ^ 7 =
      dupUXZ E X Z * dupFZ E X Z + dupVXZ E X Z * dupGZ E X Z := by
  have hq :
      (dupDZ E : ℚ) * (X : ℚ) ^ 7 =
        (dupUXZ E X Z : ℚ) * (dupFZ E X Z : ℚ)
          + (dupVXZ E X Z : ℚ) * (dupGZ E X Z : ℚ) := by
    rw [dupDZ_spec, dupUXZ_spec, dupVXZ_spec, dupFZ_spec, dupGZ_spec]
    have h := dup_bezoutX_Q E (X : ℚ) (Z : ℚ)
    linear_combination (norm := ring1) ((dupClearDen E : ℚ) ^ 2) * h
  exact_mod_cast hq

private lemma dup_bezoutZ_Z
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    dupDZ E * Z ^ 7 =
      dupUZZ E X Z * dupFZ E X Z + dupVZZ E X Z * dupGZ E X Z := by
  have hq :
      (dupDZ E : ℚ) * (Z : ℚ) ^ 7 =
        (dupUZZ E X Z : ℚ) * (dupFZ E X Z : ℚ)
          + (dupVZZ E X Z : ℚ) * (dupGZ E X Z : ℚ) := by
    rw [dupDZ_spec, dupUZZ_spec, dupVZZ_spec, dupFZ_spec, dupGZ_spec]
    have h := dup_bezoutZ_Q E (X : ℚ) (Z : ℚ)
    linear_combination (norm := ring1) ((dupClearDen E : ℚ) ^ 2) * h
  exact_mod_cast hq

private def dupIntegralCertificate (E : WeierstrassCurve ℚ) :
    HomogeneousBezoutCertificate where
  F := dupFZ E
  G := dupGZ E
  D := dupDZ E
  Ux := dupUXZ E
  Vx := dupVXZ E
  Uz := dupUZZ E
  Vz := dupVZZ E
  bezoutX := dup_bezoutX_Z E
  bezoutZ := dup_bezoutZ_Z E

private lemma p1q_naiveLogHeight_intCast_eq_logHeight (x : P1Q) :
    naiveLogHeightP1Q (x.X : ℚ) (x.Z : ℚ) = P1Q.logHeight x := by
  simp [naiveLogHeightP1Q, P1Q.logHeight, P1Q.mulHeight]

private lemma p1q_natAbs_coprime (x : P1Q) :
    Nat.Coprime x.X.natAbs x.Z.natAbs := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [← Int.gcd_eq_natAbs]
  exact Int.isCoprime_iff_gcd_eq_one.mp x.prim

private lemma sameQ_int_scalar (y : P1Q) (A B : ℤ)
    (h : P1Q.SameQ y (A : ℚ) (B : ℚ)) :
    ∃ n : ℤ, A = n * y.X ∧ B = n * y.Z := by
  rcases y.prim with ⟨u, v, huv⟩
  let n : ℤ := u * A + v * B
  have hq : (y.X : ℚ) * (B : ℚ) = (A : ℚ) * (y.Z : ℚ) := by
    simpa [P1Q.SameQ] using h
  refine ⟨n, ?_, ?_⟩
  · have hcross : A * y.Z = y.X * B := by exact_mod_cast hq.symm
    calc
      A = (u * y.X + v * y.Z) * A := by rw [huv]; ring
      _ = (u * A + v * B) * y.X := by
        linear_combination (norm := ring1) v * hcross
  · have hcross : y.X * B = A * y.Z := by exact_mod_cast hq
    calc
      B = (u * y.X + v * y.Z) * B := by rw [huv]; ring
      _ = (u * A + v * B) * y.Z := by
        linear_combination (norm := ring1) u * hcross

private lemma logHeight_ge_log_int_pair_sub_log_of_gcd_dvd
    (y : P1Q) {A B : ℤ} {N : ℕ}
    (hSame : P1Q.SameQ y (A : ℚ) (B : ℚ))
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hNpos : 0 < N)
    (hgcd : Nat.gcd A.natAbs B.natAbs ∣ N) :
    P1Q.logHeight y ≥ Real.log (max A.natAbs B.natAbs : ℝ) - Real.log (N : ℝ) := by
  obtain ⟨n, hA, hB⟩ := sameQ_int_scalar y A B hSame
  have hnne : n ≠ 0 := by
    intro hn
    rcases hAB with hA0 | hB0
    · apply hA0
      rw [hA, hn]
      simp
    · apply hB0
      rw [hB, hn]
      simp
  have hycop := p1q_natAbs_coprime y
  have hgcd_eq : Nat.gcd A.natAbs B.natAbs = n.natAbs := by
    rw [hA, hB, Int.natAbs_mul, Int.natAbs_mul]
    calc
      Nat.gcd (n.natAbs * y.X.natAbs) (n.natAbs * y.Z.natAbs)
          = n.natAbs * Nat.gcd y.X.natAbs y.Z.natAbs := by
            exact Nat.gcd_mul_left n.natAbs y.X.natAbs y.Z.natAbs
      _ = n.natAbs := by
        rw [hycop.gcd_eq_one]
        simp
  have hn_dvd_N : n.natAbs ∣ N := by simpa [hgcd_eq] using hgcd
  have hn_le_N : n.natAbs ≤ N := Nat.le_of_dvd hNpos hn_dvd_N
  have hmax_eq : max A.natAbs B.natAbs = n.natAbs * y.mulHeight := by
    rw [hA, hB, Int.natAbs_mul, Int.natAbs_mul]
    exact max_mul_mul_left n.natAbs y.X.natAbs y.Z.natAbs
  have hmax_eqR : (max A.natAbs B.natAbs : ℝ) =
      (n.natAbs : ℝ) * (y.mulHeight : ℝ) := by
    exact_mod_cast hmax_eq
  have hmax_le : (max A.natAbs B.natAbs : ℝ) ≤
      (N : ℝ) * (y.mulHeight : ℝ) := by
    rw [hmax_eqR]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn_le_N) (by positivity)
  have hmax_pos_nat : 0 < max A.natAbs B.natAbs := by
    rcases hAB with hA0 | hB0
    · exact lt_of_lt_of_le (Int.natAbs_pos.mpr hA0) (le_max_left _ _)
    · exact lt_of_lt_of_le (Int.natAbs_pos.mpr hB0) (le_max_right _ _)
  have hmax_pos : 0 < (max A.natAbs B.natAbs : ℝ) := by
    exact_mod_cast hmax_pos_nat
  have hypos : 0 < (y.mulHeight : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (P1Q.one_le_mulHeight y))
  have hlog_le : Real.log (max A.natAbs B.natAbs : ℝ) ≤
      Real.log ((N : ℝ) * (y.mulHeight : ℝ)) :=
    Real.log_le_log hmax_pos hmax_le
  have hlog_prod : Real.log ((N : ℝ) * (y.mulHeight : ℝ)) =
      Real.log (N : ℝ) + Real.log (y.mulHeight : ℝ) := by
    rw [Real.log_mul]
    · exact_mod_cast ne_of_gt hNpos
    · exact ne_of_gt hypos
  dsimp [P1Q.logHeight]
  linarith

private lemma dupDZ_ne_zero
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    dupDZ E ≠ 0 := by
  intro hD
  have hq : ((dupClearDen E : ℚ) ^ 2) * E.Δ ^ 2 = 0 := by
    have hspec := dupDZ_spec E
    rw [hD] at hspec
    exact hspec.symm
  have hL : (dupClearDen E : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt (dupClearDen_pos E)
  exact (mul_ne_zero (pow_ne_zero 2 hL) (pow_ne_zero 2 E.isUnit_Δ.ne_zero)) hq

private lemma dupFG_not_both_zero
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (x : P1Q) :
    dupFZ E x.X x.Z ≠ 0 ∨ dupGZ E x.X x.Z ≠ 0 := by
  by_contra h
  push Not at h
  have hDX := dup_bezoutX_Z E x.X x.Z
  have hDZ := dup_bezoutZ_Z E x.X x.Z
  rw [h.1, h.2] at hDX hDZ
  have hDne : dupDZ E ≠ 0 := dupDZ_ne_zero E
  have hX0 : x.X = 0 := by
    have hxpow : x.X ^ 7 = 0 := by
      exact (mul_eq_zero.mp (by simpa using hDX)).resolve_left hDne
    exact (pow_eq_zero_iff (by norm_num : (7 : ℕ) ≠ 0)).mp hxpow
  have hZ0 : x.Z = 0 := by
    have hzpow : x.Z ^ 7 = 0 := by
      exact (mul_eq_zero.mp (by simpa using hDZ)).resolve_left hDne
    exact (pow_eq_zero_iff (by norm_num : (7 : ℕ) ≠ 0)).mp hzpow
  rcases x.not_both_zero with hX | hZ
  · exact hX hX0
  · exact hZ hZ0

private lemma sameQ_clear_dup
    (E : WeierstrassCurve ℚ) (x y : P1Q)
    (hSame : P1Q.SameQ y
      (dupNumH E (x.X : ℚ) (x.Z : ℚ))
      (dupDenH E (x.X : ℚ) (x.Z : ℚ))) :
    P1Q.SameQ y (dupFZ E x.X x.Z : ℚ) (dupGZ E x.X x.Z : ℚ) := by
  rw [dupFZ_spec, dupGZ_spec]
  dsimp [P1Q.SameQ] at hSame ⊢
  linear_combination (norm := ring1) (dupClearDen E : ℚ) * hSame

private lemma log_clear_pair_ge_raw
    (E : WeierstrassCurve ℚ) (x : P1Q) :
    Real.log (max (dupFZ E x.X x.Z).natAbs (dupGZ E x.X x.Z).natAbs : ℝ) ≥
      naiveLogHeightP1Q
        (dupNumH E (x.X : ℚ) (x.Z : ℚ))
        (dupDenH E (x.X : ℚ) (x.Z : ℚ)) := by
  let L : ℝ := dupClearDen E
  let F : ℝ := dupNumH E (x.X : ℚ) (x.Z : ℚ)
  let G : ℝ := dupDenH E (x.X : ℚ) (x.Z : ℚ)
  have hLpos_nat : 0 < dupClearDen E := dupClearDen_pos E
  have hLge1 : (1 : ℝ) ≤ L := by
    dsimp [L]
    exact_mod_cast hLpos_nat
  have hFabs :
      ((dupFZ E x.X x.Z).natAbs : ℝ) = L * |F| := by
    rw [show ((dupFZ E x.X x.Z).natAbs : ℝ) =
        |((dupFZ E x.X x.Z : ℤ) : ℝ)| by
          simpa using (Nat.cast_natAbs (α := ℝ) (dupFZ E x.X x.Z))]
    have hspecQ := dupFZ_spec E x.X x.Z
    have hspecR :
        ((dupFZ E x.X x.Z : ℤ) : ℝ) = L * F := by
      dsimp [L, F]
      exact_mod_cast hspecQ
    rw [hspecR]
    rw [abs_mul]
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      positivity
    rw [abs_of_nonneg hLnonneg]
  have hGabs :
      ((dupGZ E x.X x.Z).natAbs : ℝ) = L * |G| := by
    rw [show ((dupGZ E x.X x.Z).natAbs : ℝ) =
        |((dupGZ E x.X x.Z : ℤ) : ℝ)| by
          simpa using (Nat.cast_natAbs (α := ℝ) (dupGZ E x.X x.Z))]
    have hspecQ := dupGZ_spec E x.X x.Z
    have hspecR :
        ((dupGZ E x.X x.Z : ℤ) : ℝ) = L * G := by
      dsimp [L, G]
      exact_mod_cast hspecQ
    rw [hspecR]
    rw [abs_mul]
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      positivity
    rw [abs_of_nonneg hLnonneg]
  have hmax :
      (max (dupFZ E x.X x.Z).natAbs (dupGZ E x.X x.Z).natAbs : ℝ) =
        L * max |F| |G| := by
    rw [hFabs, hGabs]
    exact (mul_max_of_nonneg |F| |G| (by positivity)).symm
  by_cases hraw0 : max |F| |G| = 0
  · have hleft :
        (max (dupFZ E x.X x.Z).natAbs (dupGZ E x.X x.Z).natAbs : ℝ) = 0 := by
      rw [hmax, hraw0, mul_zero]
    rw [hleft]
    simp [naiveLogHeightP1Q, F, G, hraw0]
  · have hrawpos : 0 < max |F| |G| := by
      have hnonneg : 0 ≤ max |F| |G| :=
        le_trans (abs_nonneg F) (le_max_left |F| |G|)
      exact lt_of_le_of_ne hnonneg (Ne.symm hraw0)
    have hraw_le_clear : max |F| |G| ≤ L * max |F| |G| :=
      le_mul_of_one_le_left (le_of_lt hrawpos) hLge1
    have hlog := Real.log_le_log hrawpos hraw_le_clear
    rw [hmax]
    simpa [naiveLogHeightP1Q, F, G] using hlog

/--
The true projective height lower bound after cancellation.

This is the audit §3 bridge: start from
`dup_projective_height_lower_height_api_seam`, prove the integer gcd/resultant cancellation
bound including `G = 0`, and convert raw pair height to primitive `P1Q.logHeight`.
-/
theorem dup_projective_height_lower_from_raw_gcd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y : P1Q,
        P1Q.SameQ y
          (dupNumH E (x.X : ℚ) (x.Z : ℚ))
          (dupDenH E (x.X : ℚ) (x.Z : ℚ)) →
        P1Q.logHeight y ≥ 4 * P1Q.logHeight x - C := by
  obtain ⟨C0, hraw⟩ := dup_projective_height_lower_height_api_seam E
  let N : ℕ := (dupDZ E).natAbs
  let Cbase : ℝ := C0 + Real.log (N : ℝ)
  refine ⟨max Cbase 0, le_max_right Cbase 0, ?_⟩
  intro x y hSame
  have hxpair : ((x.X : ℚ), (x.Z : ℚ)) ≠ (0, 0) := by
    intro hpair
    have hXq : (x.X : ℚ) = 0 := congrArg Prod.fst hpair
    have hZq : (x.Z : ℚ) = 0 := congrArg Prod.snd hpair
    have hX : x.X = 0 := by exact_mod_cast hXq
    have hZ : x.Z = 0 := by exact_mod_cast hZq
    rcases x.not_both_zero with hXne | hZne
    · exact hXne hX
    · exact hZne hZ
  have hraw_bound :=
    hraw (x.X : ℚ) (x.Z : ℚ) hxpair
  rw [p1q_naiveLogHeight_intCast_eq_logHeight x] at hraw_bound
  have hNpos : 0 < N := by
    dsimp [N]
    exact Int.natAbs_pos.mpr (dupDZ_ne_zero E)
  have hfg_ne : dupFZ E x.X x.Z ≠ 0 ∨ dupGZ E x.X x.Z ≠ 0 :=
    dupFG_not_both_zero E x
  have hgcd :
      Nat.gcd (dupFZ E x.X x.Z).natAbs (dupGZ E x.X x.Z).natAbs ∣ N := by
    dsimp [N]
    exact
      (dupIntegralCertificate E).gcd_dvd_D_natAbs_of_natAbs_coprime
        (X := x.X) (Z := x.Z) (p1q_natAbs_coprime x)
  have hSameZ : P1Q.SameQ y (dupFZ E x.X x.Z : ℚ) (dupGZ E x.X x.Z : ℚ) :=
    sameQ_clear_dup E x y hSame
  have hproj :=
    logHeight_ge_log_int_pair_sub_log_of_gcd_dvd
      y hSameZ hfg_ne hNpos hgcd
  have hclear := log_clear_pair_ge_raw E x
  have hout_raw :
      P1Q.logHeight y ≥
        naiveLogHeightP1Q
          (dupNumH E (x.X : ℚ) (x.Z : ℚ))
          (dupDenH E (x.X : ℚ) (x.Z : ℚ)) - Real.log (N : ℝ) := by
    linarith
  have hbase :
      P1Q.logHeight y ≥ 4 * P1Q.logHeight x - Cbase := by
    dsimp [Cbase]
    linarith
  have hCge : Cbase ≤ max Cbase 0 := le_max_left Cbase 0
  linarith

theorem xHeight_double_lower
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ P : (E⁄ℚ).Point,
        xHeight E (2 • P) ≥ 4 * xHeight E P - C := by
  obtain ⟨C, hC0, hC⟩ := dup_projective_height_lower_from_raw_gcd E
  refine ⟨C, hC0, ?_⟩
  intro P
  exact hC (xRep E P) (xRep E (2 • P)) (xRep_two_nsmul_same_dup E P)

private lemma dyadicOrbit_finite_of_torsion
    {G : Type*} [AddCommGroup G] {P : G}
    (hP : P ∈ AddCommGroup.torsion G) :
    ({Q : G | ∃ k : ℕ, Q = (2 ^ k : ℕ) • P} : Set G).Finite := by
  classical
  have hfinOrder : IsOfFinAddOrder P := (AddCommGroup.mem_torsion P).mp hP
  have hpos : 0 < addOrderOf P := hfinOrder.addOrderOf_pos
  let S : Finset G := (Finset.range (addOrderOf P)).image fun m => m • P
  have hS : (S : Set G).Finite := S.finite_toSet
  refine hS.subset ?_
  intro Q hQ
  rcases hQ with ⟨k, rfl⟩
  simp only [S, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
  refine ⟨(2 ^ k) % addOrderOf P, Nat.mod_lt _ hpos, ?_⟩
  exact mod_addOrderOf_nsmul P (2 ^ k)

private lemma torsion_height_le_of_doubling
    {G : Type*} [AddCommGroup G] (height : G → ℝ) (C : ℝ)
    (hdouble : ∀ Q : G, height (2 • Q) ≥ 4 * height Q - C)
    {P : G} (hP : P ∈ AddCommGroup.torsion G) :
    height P ≤ C / 3 := by
  classical
  let S : Set G := {Q | ∃ k : ℕ, Q = (2 ^ k : ℕ) • P}
  have hSfin : S.Finite := dyadicOrbit_finite_of_torsion (G := G) hP
  have hSnonempty : S.Nonempty := ⟨P, by refine ⟨0, ?_⟩; simp⟩
  obtain ⟨Q, hQ, hmax⟩ := Set.exists_max_image S height hSfin hSnonempty
  have h2Q : 2 • Q ∈ S := by
    rcases hQ with ⟨k, rfl⟩
    refine ⟨k + 1, ?_⟩
    rw [← mul_nsmul, pow_succ', Nat.mul_comm]
  have hlemax : height (2 • Q) ≤ height Q := hmax (2 • Q) h2Q
  have hlower : 4 * height Q - C ≤ height (2 • Q) := hdouble Q
  have hQle : height Q ≤ C / 3 := by linarith
  have hPmem : P ∈ S := by refine ⟨0, ?_⟩; simp
  have hPleQ : height P ≤ height Q := hmax P hPmem
  exact le_trans hPleQ hQle

private lemma finite_torsion_of_northcott_double_lower
    {G : Type*} [AddCommGroup G] (height : G → ℝ) (C : ℝ)
    [Northcott height]
    (hdouble : ∀ Q : G, height (2 • Q) ≥ 4 * height Q - C) :
    (AddCommGroup.torsion G : Set G).Finite := by
  refine (Northcott.finite_le (h := height) (C / 3)).subset ?_
  intro P hP
  exact torsion_height_le_of_doubling height C hdouble hP

theorem rational_torsion_finite_height (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite := by
  obtain ⟨C, _hC0, hC⟩ := xHeight_double_lower E
  haveI : Northcott (xHeight E) := xHeight_northcott E
  exact finite_torsion_of_northcott_double_lower (xHeight E) C hC

end MazurProof
