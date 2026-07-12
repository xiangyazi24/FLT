import FLT.Assumptions.MazurProof.N18Block5FormalKernel
import FLT.Assumptions.MazurProof.N18RouteC_Isogeny
import FLT.Assumptions.MazurProof.N18RouteC_ThreeAdic
import FLT.Assumptions.MazurProof.N18RouteC_Reduction
import FLT.Assumptions.MazurProof.N18RouteC_Block4
import FLT.Assumptions.MazurProof.N18RouteC_Composition
import FLT.Assumptions.MazurProof.CyclicExclusion18

/-!
# N18 Block-5 instantiation — `FormalKernelData → no_obstruction18`

This file instantiates the *verified* abstract Block-5 scaffold
(`FormalKernel18`, providing the proven `no_prime_to_3_torsion`,
`three_power_torsion_exponent_three`, `annihilated_by_21`) for the real
`E₀ = 162.c3` over `L = ℚ(ζ₉)⁺` at the prime `π ∣ 3`, and closes
`CyclicExclusion18.no_obstruction18` **conditional on exactly three carried
packages** (Package I `add_congr`, Package II `msq_torsionFree`,
Package III `three_pow_torsion_mem_kernel`) plus the elementary `zParam`
laws and a carried `front_end` bridge.

Everything else — the `FormalKernel18` instance, the reduction of `[21]`
annihilation to the three abstract lemmas, and the assembly — is **proved**
here, with clearly-labelled `sorry`s for the pure valuation inductions
(`val_unit_smul`, `val_three_smul_ge`), the `hQ7` reduction-chaining, and the
rank-0 `torsion_eq_Z21` bookkeeping.  See
`N18_BLOCK5_INSTANTIATION_DESIGN.md`.
-/

open scoped Classical

namespace MazurProof.N18Block5Instantiation

open MazurProof.N18RouteC
open MazurProof.N18RouteC.Isogeny

noncomputable section

/-! ## `WithTop ℤ → ℕ∞` coercion (negatives, absent on the kernel, clamp to `0`). -/

/-- Push a `WithTop ℤ` valuation into `ℕ∞`.  On the formal kernel every value is
`≥ 1` or `⊤`, so no information is lost. -/
def toENat (x : WithTop ℤ) : ℕ∞ := x.map Int.toNat

@[simp] theorem toENat_top : toENat (⊤ : WithTop ℤ) = ⊤ := rfl

theorem toENat_eq_top {x : WithTop ℤ} : toENat x = ⊤ ↔ x = ⊤ := by
  cases x with
  | top => exact iff_of_true rfl rfl
  | coe n =>
      refine iff_of_false ?_ WithTop.coe_ne_top
      show (↑n : WithTop ℤ).map Int.toNat ≠ ⊤
      rw [WithTop.map_coe]
      exact WithTop.coe_ne_top

@[simp] theorem toENat_one : toENat (1 : WithTop ℤ) = 1 := rfl

theorem one_le_toENat_of_pos {x : WithTop ℤ} (hx : 0 < x) : (1 : ℕ∞) ≤ toENat x := by
  cases x with
  | top => simp
  | coe n =>
      rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
        WithTop.coe_lt_coe] at hx
      have hn : (1 : ℕ) ≤ n.toNat := by omega
      rw [show toENat (↑n : WithTop ℤ) = (↑(n.toNat) : ℕ∞) from
        WithTop.map_coe Int.toNat n]
      exact_mod_cast hn

/-! ## The carried interface -/

/-- The three carried packages plus the elementary `zParam` laws for the real
`E₀`-formal group.  `zParam P = -x/y` is the formal parameter; `vpi` is the
additive `π`-adic valuation with `vpi 3 = 3`. -/
structure FormalKernelData where
  /-- Formal parameter `z = -x/y` of a point of `E₀(L)`. -/
  zParam : E0Point → L
  /-- The additive `π`-adic valuation (`vpi π = 1`, `vpi 3 = 3`). -/
  vpi : AddValuation L (WithTop ℤ)
  vpi_three : vpi (3 : L) = (3 : WithTop ℤ)
  zParam_zero : zParam 0 = 0
  zParam_neg : ∀ P, zParam (-P) = - zParam P
  /-- `z = 0` only at the origin (faithfulness of `z = -x/y` on the kernel). -/
  zParam_eq_zero : ∀ P, zParam P = 0 → P = 0
  /-- **Package I** — integral formal group law leading term (pointwise):
  `v(z(P⊕Q) − zP − zQ) ≥ v(zP)+v(zQ)` for kernel points `P, Q`. -/
  add_congr : ∀ P Q, 0 < vpi (zParam P) → 0 < vpi (zParam Q) →
    vpi (zParam P) + vpi (zParam Q) ≤ vpi (zParam (P + Q) - zParam P - zParam Q)
  /-- **Package II** — `Ê₀(𝔪²)` torsion-free: a nonzero kernel torsion point has
  valuation exactly `1`. -/
  msq_torsionFree : ∀ P, 0 < vpi (zParam P) → zParam P ≠ 0 →
    (∃ n : ℕ, 0 < n ∧ n • P = 0) → vpi (zParam P) = 1
  /-- **Package III** — supersingular `⇒` `3`-power torsion lands in the formal
  kernel. -/
  three_pow_torsion_mem_kernel : ∀ P, (∃ k : ℕ, ((3 : ℤ) ^ k) • P = 0) →
    0 < vpi (zParam P)

namespace FormalKernelData

variable (D : FormalKernelData)

/-! ## The formal kernel as an additive subgroup of `E₀(L)` -/

/-- The formal kernel `Ê₀(𝔪) = {P | v(zP) > 0}`, an additive subgroup by
Package I (`add_congr`) and `zParam_neg`. -/
def kernelSubgroup : AddSubgroup E0Point where
  carrier := {P | 0 < D.vpi (D.zParam P)}
  zero_mem' := by
    show 0 < D.vpi (D.zParam 0)
    rw [D.zParam_zero, AddValuation.map_zero]
    simpa using WithTop.coe_lt_top (0 : ℤ)
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have hr :
        D.vpi (D.zParam a) + D.vpi (D.zParam b) ≤
          D.vpi (D.zParam (a + b) - D.zParam a - D.zParam b) :=
      D.add_congr a b ha hb
    have hpos_sum : 0 < D.vpi (D.zParam a) + D.vpi (D.zParam b) :=
      lt_of_lt_of_le ha (le_add_of_nonneg_right (le_of_lt hb))
    have hrpos : 0 < D.vpi (D.zParam (a + b) - D.zParam a - D.zParam b) :=
      lt_of_lt_of_le hpos_sum hr
    have hsum : 0 < D.vpi (D.zParam a + D.zParam b) := D.vpi.map_lt_add ha hb
    have hdecomp :
        D.zParam (a + b) =
          (D.zParam (a + b) - D.zParam a - D.zParam b) +
            (D.zParam a + D.zParam b) := by ring
    rw [hdecomp]
    exact D.vpi.map_lt_add hrpos hsum
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [D.zParam_neg, AddValuation.map_neg]
    exact ha

theorem mem_kernelSubgroup {P : E0Point} :
    P ∈ D.kernelSubgroup ↔ 0 < D.vpi (D.zParam P) := Iff.rfl

/-! ## The `FormalKernel18` instance -/

/-- Instantiate the abstract Block-5 scaffold for the real `E₀`. -/
def formalKernel18 : FormalKernel18 where
  M := D.kernelSubgroup
  addCommGroup := inferInstance
  val := fun z => toENat (D.vpi (D.zParam (z : E0Point)))
  val_eq_top := by
    intro z
    show toENat (D.vpi (D.zParam (z : E0Point))) = ⊤ ↔ z = 0
    rw [toENat_eq_top, D.vpi.top_iff]
    constructor
    · intro h
      exact Subtype.ext (by
        rw [ZeroMemClass.coe_zero]; exact D.zParam_eq_zero _ h)
    · intro h
      have : (z : E0Point) = 0 := by rw [h, ZeroMemClass.coe_zero]
      rw [this, D.zParam_zero]
  one_le_val := by
    intro z _
    exact one_le_toENat_of_pos z.property
  val_unit_smul := by
    -- WIRING (valuation induction): `[m]` for `3 ∤ m` preserves `v(z)` because
    -- `z([m]P) = m·zP + (higher order)` and `v(m) = 0`.  Derived from `add_congr`
    -- by induction (`zParam_nsmul_congr`); left as a labelled `sorry`.
    intro m hm z
    sorry
  val_three_smul_ge := by
    -- WIRING (valuation induction): `z([3]P) = 3zP + zP²·A(zP)`, `v(3) = 3`.
    -- Derived from `add_congr` + `vpi_three`; left as a labelled `sorry`.
    intro z
    sorry
  torsion_val_eq_one := by
    intro z hz htor
    show toENat (D.vpi (D.zParam (z : E0Point))) = 1
    have hpos : 0 < D.vpi (D.zParam (z : E0Point)) := z.property
    have hzne : D.zParam (z : E0Point) ≠ 0 := by
      intro h
      exact hz (Subtype.ext (by
        rw [ZeroMemClass.coe_zero]; exact D.zParam_eq_zero _ h))
    obtain ⟨n, hn, hnz⟩ := htor
    have hnzc : n • (z : E0Point) = 0 := by
      have := congrArg (Subtype.val) hnz
      rwa [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero] at this
    have hv1 : D.vpi (D.zParam (z : E0Point)) = 1 :=
      D.msq_torsionFree _ hpos hzne ⟨n, hn, hnzc⟩
    rw [hv1, toENat_one]

/-! ## Assembly of `[21]`-annihilation -/

-- `D` is used only inside the tactic proofs below, so it must be `include`d.
include D

/-- **Lemma C wiring.**  A `3`-power torsion point is killed by `[3]`: Package III
puts it in the formal kernel, then the proven
`three_power_torsion_exponent_three` applies. -/
theorem hC (x : E0Point) (hx : ∃ k : ℕ, ((3 : ℤ) ^ k) • x = 0) :
    (3 : ℤ) • x = 0 := by
  have hmem : x ∈ D.kernelSubgroup :=
    (D.mem_kernelSubgroup).mpr (D.three_pow_torsion_mem_kernel x hx)
  set z : (D.kernelSubgroup) := ⟨x, hmem⟩ with hzdef
  obtain ⟨k, hk⟩ := hx
  -- rewrite the `ℤ`-power hypothesis as a `ℕ`-multiplication
  have hknat : ((3 : ℕ) ^ k) • x = 0 := by
    have : ((3 : ℤ) ^ k) • x = (((3 : ℕ) ^ k : ℕ) : ℤ) • x := by
      norm_cast
    rw [this, natCast_zsmul] at hk
    exact hk
  have hkz : ((3 : ℕ) ^ k) • z = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, hzdef]
    exact hknat
  have h3z : (3 : ℤ) • z = 0 :=
    (D.formalKernel18).three_power_torsion_exponent_three z k hkz
  have := congrArg (Subtype.val) h3z
  rwa [AddSubgroupClass.coe_zsmul, ZeroMemClass.coe_zero] at this

/-- **Lemma A + reduction wiring (`hQ7`).**  The prime-to-`3` part of `E₀(L)`
injects into the seven-point reduction (`Reduction.seven_nsmul`), so it is killed
by `[7]`.  The reduction-homomorphism chaining is left as a labelled `sorry`. -/
theorem hQ (x : E0Point) (hx : ∃ j : ℤ, ¬ (3 ∣ j) ∧ j • x = 0) :
    (7 : ℤ) • x = 0 := by
  -- WIRING (hQ7 red-chaining): Lemma A (`no_prime_to_3_torsion`) rules out
  -- prime-to-3 torsion inside the formal kernel; the residual injects into
  -- `Reduction.RedPoint` (card 7) via the reduction map, whence `[7]`.
  sorry

/-- `[21]` annihilates every torsion point of `E₀(L)`, via the proven abstract
`annihilated_by_21` fed with `hC` and `hQ`. -/
theorem torsion_annihilated_by_21 (x : E0Point)
    (htor : ∃ n : ℕ, 0 < n ∧ n • x = 0) : (21 : ℤ) • x = 0 :=
  FormalKernel18.annihilated_by_21 (G := E0Point) D.hC D.hQ x htor

/-- **Rank-0 wiring (`torsion_eq_Z21`).**  Combined with `Block4.weak_three_descent`
(every point is a kernel representative mod `3`) and the upstream rank-0 input,
every `L`-point is torsion and hence killed by `[21]`.  Left as a labelled
`sorry`. -/
theorem all_points_annihilated_by_21 : ∀ P : E0Point, (21 : ℤ) • P = 0 := by
  -- Every `P` is torsion (rank 0); then `torsion_annihilated_by_21`.
  -- `Block4.weak_three_descent P : ∃ h, 3•h = 0 ∧ ∃ Q, P = h + 3•Q`.
  sorry

/-- **Closing `no_obstruction18`, conditional on the carried `front_end`.**
`front_end` is the committed geometric bridge `E₀(L)=ℤ/21 ⇒ ¬Obstruction18`
(`X₁(18)` split / Jacobian / five-descent). -/
theorem no_obstruction18
    (front_end : (∀ P : E0Point, (21 : ℤ) • P = 0) →
      ¬ ∃ b c X : ℚ, MazurProof.CyclicExclusion18.Obstruction18 b c X) :
    ¬ ∃ b c X : ℚ, MazurProof.CyclicExclusion18.Obstruction18 b c X :=
  front_end D.all_points_annihilated_by_21

end FormalKernelData

end

end MazurProof.N18Block5Instantiation
