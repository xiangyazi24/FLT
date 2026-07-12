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
here.  The two pure valuation inductions `val_unit_smul` and `val_three_smul_ge`
are now **discharged** from Package I (`add_congr`) via `zParam_nsmul_congr`
plus the elementary `vpi_three`/`vpi_unit` laws.  Two labelled `sorry`s remain,
both blocked on infrastructure absent from the committed RouteC files:
* `hQ` (the `hQ7` prime-to-3 reduction chaining) needs a concrete reduction
  homomorphism `red : E0Point →+ Reduction.RedPoint` with
  `red.ker = kernelSubgroup` — RouteC only takes such a `red` as a hypothesis
  (`Block7`/`Separated`), it never constructs it;
* `all_points_annihilated_by_21` (rank-0 `torsion_eq_Z21` bookkeeping) needs an
  unconditional "every `E₀(L)`-point is torsion" (rank-0 / finiteness) input,
  which is likewise not present unconditionally in the committed infra.
See `N18_BLOCK5_INSTANTIATION_DESIGN.md`.
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

theorem toENat_coe (m : ℤ) : toENat (↑m) = (↑m.toNat : ℕ∞) :=
  WithTop.map_coe Int.toNat m

theorem toENat_mono {x y : WithTop ℤ} (h : x ≤ y) : toENat x ≤ toENat y := by
  cases x with
  | top => rw [top_le_iff.mp h]
  | coe a =>
      cases y with
      | top => exact le_top
      | coe b =>
          rw [WithTop.coe_le_coe] at h
          rw [toENat_coe, toENat_coe]
          exact_mod_cast Int.toNat_le_toNat h

theorem toENat_min {x y : WithTop ℤ} : toENat (min x y) = min (toENat x) (toENat y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (toENat_mono h)]
  · rw [min_eq_right h, min_eq_right (toENat_mono h)]

theorem toENat_three_add {a : WithTop ℤ} (ha : 0 ≤ a) :
    toENat (3 + a) = 3 + toENat a := by
  cases a with
  | top => simp
  | coe m =>
      have hm : (0 : ℤ) ≤ m := by exact_mod_cast ha
      rw [show (3 : WithTop ℤ) = ((3 : ℤ) : WithTop ℤ) by norm_cast, ← WithTop.coe_add,
        toENat_coe, toENat_coe]
      have h3 : (3 + m).toNat = 3 + m.toNat := by omega
      rw [h3, Nat.cast_add, Nat.cast_ofNat]

theorem toENat_two_nsmul {a : WithTop ℤ} (ha : 0 ≤ a) :
    toENat (2 • a) = 2 * toENat a := by
  cases a with
  | top => simp [two_nsmul]
  | coe m =>
      have hm : (0 : ℤ) ≤ m := by exact_mod_cast ha
      rw [two_nsmul, ← WithTop.coe_add, toENat_coe, toENat_coe]
      have hmm : (m + m).toNat = 2 * m.toNat := by omega
      rw [hmm, Nat.cast_mul, Nat.cast_ofNat]

theorem lt_two_nsmul {x : WithTop ℤ} (hx : 0 < x) (hne : x ≠ ⊤) : x < 2 • x := by
  obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
  have hm : (0 : ℤ) < m := by exact_mod_cast hx
  rw [two_nsmul, ← WithTop.coe_add, WithTop.coe_lt_coe]
  omega

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
  /-- Elementary π-adic unit law (same tier as `vpi_three`): an integer prime to
  `3` is a `π`-unit, so it has valuation `0`.  On the real `E₀` this is
  `ThreeAdic.ordPi m = 0` for `3 ∤ m`; carried here because `vpi` is abstract. -/
  vpi_unit : ∀ m : ℤ, ¬ (3 ∣ m) → vpi ((m : L)) = 0
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

/-! ## Valuation inductions for `zParam` (Package I `add_congr` closure) -/

/-- The additive valuation is nonnegative on `ℕ`-casts. -/
theorem zero_le_vpi_natCast (k : ℕ) : (0 : WithTop ℤ) ≤ D.vpi ((k : L)) := by
  induction k with
  | zero => rw [Nat.cast_zero, D.vpi.map_zero]; exact le_top
  | succ n ih =>
      rw [Nat.cast_succ]
      exact D.vpi.map_le_add ih (le_of_eq D.vpi.map_one.symm)

/-- **Formal-group `nsmul` congruence** (from Package I `add_congr`): for a kernel
point `P` (`0 < v(zP)`), the parameter of `[n]P` agrees with `n·zP` up to a term
of valuation `≥ 2·v(zP)`, and `[n]P` stays in the kernel. -/
theorem zParam_nsmul_congr (P : E0Point) (hpos : 0 < D.vpi (D.zParam P)) :
    ∀ n : ℕ, 1 ≤ n →
      2 • D.vpi (D.zParam P) ≤ D.vpi (D.zParam (n • P) - n • D.zParam P)
      ∧ D.vpi (D.zParam P) ≤ D.vpi (D.zParam (n • P)) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by norm_num)
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · refine ⟨?_, ?_⟩
        · rw [zero_add, one_nsmul, one_nsmul, sub_self, D.vpi.map_zero]; exact le_top
        · rw [zero_add, one_nsmul]
      · obtain ⟨ih1, ih2⟩ := ih hk
        have hkP : 0 < D.vpi (D.zParam (k • P)) := lt_of_lt_of_le hpos ih2
        have hB1 : 2 • D.vpi (D.zParam P)
            ≤ D.vpi (D.zParam (k • P + P) - D.zParam (k • P) - D.zParam P) := by
          have h2 : 2 • D.vpi (D.zParam P)
              ≤ D.vpi (D.zParam (k • P)) + D.vpi (D.zParam P) := by
            rw [two_nsmul]; exact add_le_add ih2 le_rfl
          exact le_trans h2 (D.add_congr (k • P) P hkP hpos)
        have key : D.zParam ((k + 1) • P) - (k + 1) • D.zParam P
            = (D.zParam (k • P + P) - D.zParam (k • P) - D.zParam P)
              + (D.zParam (k • P) - k • D.zParam P) := by
          rw [succ_nsmul P k, succ_nsmul (D.zParam P) k]; abel
        have hclaim1 : 2 • D.vpi (D.zParam P)
            ≤ D.vpi (D.zParam ((k + 1) • P) - (k + 1) • D.zParam P) := by
          rw [key]; exact D.vpi.map_le_add hB1 ih1
        refine ⟨hclaim1, ?_⟩
        have hval_smul : D.vpi (D.zParam P) ≤ D.vpi ((k + 1) • D.zParam P) := by
          rw [nsmul_eq_mul, D.vpi.map_mul]
          exact le_add_of_nonneg_left (D.zero_le_vpi_natCast (k + 1))
        have ha_le : D.vpi (D.zParam P) ≤ 2 • D.vpi (D.zParam P) := by
          rw [two_nsmul]; exact le_add_of_nonneg_left (le_of_lt hpos)
        have hdecomp : D.zParam ((k + 1) • P)
            = (D.zParam ((k + 1) • P) - (k + 1) • D.zParam P) + (k + 1) • D.zParam P := by
          abel
        rw [hdecomp]
        exact D.vpi.map_le_add (le_trans ha_le hclaim1) hval_smul

/-- **`[m]` preserves the parameter valuation for `3 ∤ m`** (ℕ version). -/
theorem vpi_zParam_nsmul (P : E0Point) (hpos : 0 < D.vpi (D.zParam P))
    (n : ℕ) (hn : ¬ (3 ∣ (n : ℤ))) :
    D.vpi (D.zParam (n • P)) = D.vpi (D.zParam P) := by
  rcases eq_or_ne (D.zParam P) 0 with h0 | hfP
  · have hP0 : P = 0 := D.zParam_eq_zero P h0
    rw [hP0, smul_zero]
  · have hane : D.vpi (D.zParam P) ≠ ⊤ := by rw [D.vpi.ne_top_iff]; exact hfP
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exact absurd (by norm_num) hn
      · exact h
    obtain ⟨c1, _c2⟩ := D.zParam_nsmul_congr P hpos n hn1
    have hunit : D.vpi ((n : L)) = 0 := by
      simpa using D.vpi_unit (n : ℤ) hn
    have hnfP : D.vpi (n • D.zParam P) = D.vpi (D.zParam P) := by
      rw [nsmul_eq_mul, D.vpi.map_mul, hunit, zero_add]
    have hlt : D.vpi (n • D.zParam P)
        < D.vpi (D.zParam (n • P) - n • D.zParam P) := by
      rw [hnfP]
      exact lt_of_lt_of_le (lt_two_nsmul hpos hane) c1
    have hdecomp : D.zParam (n • P)
        = n • D.zParam P + (D.zParam (n • P) - n • D.zParam P) := by abel
    rw [hdecomp, D.vpi.map_add_eq_of_lt_left hlt, hnfP]

/-- **`[m]` preserves the parameter valuation for `3 ∤ m`** (ℤ version). -/
theorem vpi_zParam_zsmul (P : E0Point) (hpos : 0 < D.vpi (D.zParam P))
    (m : ℤ) (hm : ¬ (3 ∣ m)) :
    D.vpi (D.zParam (m • P)) = D.vpi (D.zParam P) := by
  rcases le_total 0 m with hmnn | hmp
  · lift m to ℕ using hmnn with n
    rw [natCast_zsmul]
    exact D.vpi_zParam_nsmul P hpos n hm
  · have hnn : (0 : ℤ) ≤ -m := by omega
    have e2 : ((-m).toNat) • P = (-m) • P := by
      rw [← natCast_zsmul, Int.toNat_of_nonneg hnn]
    have hmP : m • P = -(((-m).toNat) • P) := by rw [e2, neg_zsmul, neg_neg]
    rw [hmP, D.zParam_neg, D.vpi.map_neg]
    apply D.vpi_zParam_nsmul P hpos
    rw [Int.toNat_of_nonneg hnn, Int.dvd_neg]
    exact hm

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
    -- `[m]` for `3 ∤ m` preserves `v(z)`: `z([m]P) = m·zP + (higher order)` and
    -- `v(m) = 0` (`vpi_unit`).  Strict domination via `zParam_nsmul_congr`.
    intro m hm z
    have hcoe : ((m • z : D.kernelSubgroup) : E0Point) = m • (z : E0Point) := by
      rw [AddSubgroupClass.coe_zsmul]
    show toENat (D.vpi (D.zParam ((m • z : D.kernelSubgroup) : E0Point)))
       = toENat (D.vpi (D.zParam ((z : D.kernelSubgroup) : E0Point)))
    rw [hcoe]
    exact congrArg toENat (D.vpi_zParam_zsmul _ z.property m hm)
  val_three_smul_ge := by
    -- `z([3]P) = 3·zP + r`, `v(r) ≥ 2·v(zP)` (`zParam_nsmul_congr`), `v(3·zP) = 3 + v(zP)`
    -- (`vpi_three`), then `v([3]z) ≥ min(3+v, 2v)` via `map_add`, pushed through `toENat`.
    intro z
    have hpos : 0 < D.vpi (D.zParam (z : E0Point)) := z.property
    have hcoe : (((3 : ℤ) • z : D.kernelSubgroup) : E0Point) = (3 : ℕ) • (z : E0Point) := by
      rw [AddSubgroupClass.coe_zsmul, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_cast, natCast_zsmul]
    show min (3 + toENat (D.vpi (D.zParam (z : E0Point))))
          (2 * toENat (D.vpi (D.zParam (z : E0Point))))
       ≤ toENat (D.vpi (D.zParam (((3 : ℤ) • z : D.kernelSubgroup) : E0Point)))
    rw [hcoe]
    obtain ⟨c1, _c2⟩ := D.zParam_nsmul_congr (z : E0Point) hpos 3 (by norm_num)
    have hv3 : D.vpi ((3 : ℕ) • D.zParam (z : E0Point))
        = 3 + D.vpi (D.zParam (z : E0Point)) := by
      rw [nsmul_eq_mul, D.vpi.map_mul]
      congr 1
      rw [show ((3 : ℕ) : L) = (3 : L) by norm_cast]; exact D.vpi_three
    have hdecomp : D.zParam ((3 : ℕ) • (z : E0Point))
        = (3 : ℕ) • D.zParam (z : E0Point)
          + (D.zParam ((3 : ℕ) • (z : E0Point)) - (3 : ℕ) • D.zParam (z : E0Point)) := by
      abel
    have hbound : min (3 + D.vpi (D.zParam (z : E0Point)))
          (2 • D.vpi (D.zParam (z : E0Point)))
        ≤ D.vpi (D.zParam ((3 : ℕ) • (z : E0Point))) := by
      rw [hdecomp]
      exact le_trans (min_le_min (le_of_eq hv3.symm) c1) (D.vpi.map_add _ _)
    have hbridge : toENat (min (3 + D.vpi (D.zParam (z : E0Point)))
          (2 • D.vpi (D.zParam (z : E0Point))))
        = min (3 + toENat (D.vpi (D.zParam (z : E0Point))))
          (2 * toENat (D.vpi (D.zParam (z : E0Point)))) := by
      rw [toENat_min, toENat_three_add (le_of_lt hpos), toENat_two_nsmul (le_of_lt hpos)]
    calc min (3 + toENat (D.vpi (D.zParam (z : E0Point))))
            (2 * toENat (D.vpi (D.zParam (z : E0Point))))
        = toENat (min (3 + D.vpi (D.zParam (z : E0Point)))
            (2 • D.vpi (D.zParam (z : E0Point)))) := hbridge.symm
      _ ≤ toENat (D.vpi (D.zParam ((3 : ℕ) • (z : E0Point)))) := toENat_mono hbound
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
