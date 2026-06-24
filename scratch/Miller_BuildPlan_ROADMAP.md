[ask-gpt dm4 tid=173a8508 +0s] dispatched, waiting for answer
[ask-gpt dm4 tid=173a8508 +90s] waiting (status=processing)
[ask-gpt dm4 tid=173a8508 +180s] waiting (status=processing)
[ask-gpt dm4 tid=173a8508 +270s] waiting (status=processing)
[ask-gpt dm4 tid=173a8508 +360s] waiting (status=processing)
[ask-gpt dm4 tid=173a8508 +450s] waiting (status=processing)
[ask-gpt dm4 tid=173a8508 +540s] waiting (status=processing)
[ask-gpt dm4 tid=173a8508 +630s] waiting (status=processing)
[ask-gpt dm4 tid=173a8508 +720s] waiting (status=processing)
[ask-gpt dm4 tid=173a8508 +810s] waiting (status=processing)
[ask-gpt dm4 tid=173a8508 +836s] terminal: status=completed
The right answer is: **do not try to replace**

```lean
rationalWeilPairingPackage (E) (m) : E.WeilPairingPackage m := sorry
```

by a full Miller construction in `scratch/DischargeA2.lean`. The Miller construction is a **multi-week infrastructure seam**, not a SEAM2-scale discharge, unless the file already has all divisor/tame-symbol/weil-reciprocity infrastructure. What is SEAM2-scale is the **wrapper** around named primitives: pairing construction, bilinearity packaging, alternating, and the full-grid nondegeneracy transfer.

Below is the build plan I would use.

---

## 1. File-by-file construction order

Use the following order. Each file should expose only the next layer’s API; do not let `rationalWeilPairingPackage` depend on raw Miller recursion details.

### File A: `FLT/EllipticCurve/WeilPairing/DivExpr.lean`

Goal: syntactic divisors on affine elliptic-curve points.

Core API:

```lean
namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

abbrev DivExpr : Type _ := ((E⁄K).Point →₀ ℤ)

namespace DivExpr

noncomputable def degree (D : E.DivExpr) : ℤ :=
  D.sum fun _ n => n

def disjoint (D₁ D₂ : E.DivExpr) : Prop :=
  Disjoint D₁.support D₂.support

def point (P : (E⁄K).Point) : E.DivExpr :=
  Finsupp.single P 1

@[simp] theorem degree_zero :
    degree (E := E) 0 = 0 := by
  simp [degree]

@[simp] theorem degree_add (D₁ D₂ : E.DivExpr) :
    degree (E := E) (D₁ + D₂) =
      degree (E := E) D₁ + degree (E := E) D₂ := by
  classical
  simp [degree, Finsupp.sum_add_index]

@[simp] theorem degree_neg (D : E.DivExpr) :
    degree (E := E) (-D) = - degree (E := E) D := by
  classical
  simp [degree]

@[simp] theorem degree_point (P : (E⁄K).Point) :
    degree (E := E) (point (E := E) P) = 1 := by
  classical
  simp [degree, point]

end DivExpr
end WeierstrassCurve
```

Named Mathlib/FLT API used here:

```lean
Finsupp
Finsupp.single
Finsupp.support
Finsupp.sum
Finset
Disjoint
(E⁄K).Point
WeierstrassCurve.Affine.Point
```

This file should be completely elementary.

---

### File B: `FLT/EllipticCurve/WeilPairing/MillerExpr.lean`

Goal: define the syntactic rational functions and their divisor expression.

This is where Route B lives.

Suggested skeleton:

```lean
namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

inductive MillerExpr : Type _
  | one : MillerExpr
  | const : Kˣ → MillerExpr
  | line : (E⁄K).Point → (E⁄K).Point → MillerExpr
  | vertical : (E⁄K).Point → MillerExpr
  | mul : MillerExpr → MillerExpr → MillerExpr
  | inv : MillerExpr → MillerExpr

namespace MillerExpr

noncomputable def divExpr : E.MillerExpr → E.DivExpr
  | one => 0
  | const _ => 0
  | line P Q =>
      -- divisor of line through P,Q:
      -- [P] + [Q] + [-(P+Q)] - 3[O]
      sorry
  | vertical P =>
      -- divisor of vertical line through P:
      -- [P] + [-P] - 2[O]
      sorry
  | mul f g => divExpr f + divExpr g
  | inv f => - divExpr f

@[simp] theorem divExpr_one :
    divExpr (E := E) .one = 0 := rfl

@[simp] theorem divExpr_const (c : Kˣ) :
    divExpr (E := E) (.const c) = 0 := rfl

@[simp] theorem divExpr_mul (f g : E.MillerExpr) :
    divExpr (E := E) (.mul f g) =
      divExpr (E := E) f + divExpr (E := E) g := rfl

@[simp] theorem divExpr_inv (f : E.MillerExpr) :
    divExpr (E := E) (.inv f) =
      - divExpr (E := E) f := rfl

theorem degree_divExpr (f : E.MillerExpr) :
    DivExpr.degree (E := E) (divExpr (E := E) f) = 0 := by
  induction f <;> simp [divExpr, DivExpr.degree_add, DivExpr.degree_neg]
  -- line/vertical cases use the explicit divisor formulas
  all_goals sorry

end MillerExpr
end WeierstrassCurve
```

The hard input here is not the recursion itself. It is the **line and vertical divisor formulas**, especially the add/tangent cases. You said `xRep_add` is already designed elsewhere; this file should import it and expose only:

```lean
theorem divExpr_line :
    MillerExpr.divExpr (E := E) (.line P Q) =
      DivExpr.point (E := E) P +
      DivExpr.point (E := E) Q +
      DivExpr.point (E := E) (-(P + Q)) -
      3 • DivExpr.point (E := E) 0 := by
  sorry

theorem divExpr_vertical :
    MillerExpr.divExpr (E := E) (.vertical P) =
      DivExpr.point (E := E) P +
      DivExpr.point (E := E) (-P) -
      2 • DivExpr.point (E := E) 0 := by
  sorry
```

These two should be named seams until the coordinate calculations are done.

---

### File C: `FLT/EllipticCurve/WeilPairing/EvalDiv.lean`

Goal: evaluate a syntactic rational function on a degree-zero divisor with disjoint support.

The important design choice: return `Kˣ`, not `K`. Negative coefficients in a divisor require inverses.

```lean
namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

namespace MillerExpr

noncomputable def evalUnitAt
    (f : E.MillerExpr) (P : (E⁄K).Point)
    (hP : P ∉ (divExpr (E := E) f).support) : Kˣ :=
  sorry

noncomputable def evalDiv
    (f : E.MillerExpr) (D : E.DivExpr)
    (hdeg : DivExpr.degree (E := E) D = 0)
    (hdisj : Disjoint (divExpr (E := E) f).support D.support) : Kˣ :=
  ∏ P in D.support,
    (evalUnitAt (E := E) f P (by
      exact Finset.disjoint_left.mp hdisj ?_ ?_)) ^ (D P)
```

You will likely need a small helper because the proof obligation under the product is awkward:

```lean
lemma not_mem_div_support_of_mem_eval_support
    {f : E.MillerExpr} {D : E.DivExpr}
    (hdisj : Disjoint (MillerExpr.divExpr (E := E) f).support D.support)
    {P : (E⁄K).Point} (hP : P ∈ D.support) :
    P ∉ (MillerExpr.divExpr (E := E) f).support := by
  exact fun hPf => (Finset.disjoint_left.mp hdisj hPf hP)
```

First real lemmas in this layer:

```lean
@[simp] theorem evalDiv_zero
    (f : E.MillerExpr)
    (hdisj : Disjoint (MillerExpr.divExpr (E := E) f).support (0 : E.DivExpr).support) :
    evalDiv (E := E) f 0 (by simp [DivExpr.degree]) hdisj = 1 := by
  classical
  simp [evalDiv]

theorem evalDiv_add
    (f : E.MillerExpr) (D₁ D₂ : E.DivExpr)
    (hdeg₁ : DivExpr.degree (E := E) D₁ = 0)
    (hdeg₂ : DivExpr.degree (E := E) D₂ = 0)
    (hdisj₁ : Disjoint (MillerExpr.divExpr (E := E) f).support D₁.support)
    (hdisj₂ : Disjoint (MillerExpr.divExpr (E := E) f).support D₂.support) :
    evalDiv (E := E) f (D₁ + D₂)
      (by simp [DivExpr.degree_add, hdeg₁, hdeg₂])
      (by
        -- support of D₁ + D₂ is contained in union of supports
        sorry) =
    evalDiv (E := E) f D₁ hdeg₁ hdisj₁ *
    evalDiv (E := E) f D₂ hdeg₂ hdisj₂ := by
  classical
  -- `Finsupp`/`Finset.prod` bookkeeping
  sorry

theorem evalDiv_mul
    (f g : E.MillerExpr) (D : E.DivExpr)
    (hdeg : DivExpr.degree (E := E) D = 0)
    (hf : Disjoint (MillerExpr.divExpr (E := E) f).support D.support)
    (hg : Disjoint (MillerExpr.divExpr (E := E) g).support D.support) :
    evalDiv (E := E) (.mul f g) D hdeg (by
      -- support of div(f*g) contained in union
      sorry) =
    evalDiv (E := E) f D hdeg hf *
    evalDiv (E := E) g D hdeg hg := by
  classical
  sorry

theorem evalDiv_const
    (c : Kˣ) (D : E.DivExpr)
    (hdeg : DivExpr.degree (E := E) D = 0)
    (hdisj : Disjoint (MillerExpr.divExpr (E := E) (.const c)).support D.support) :
    evalDiv (E := E) (.const c) D hdeg hdisj = 1 := by
  classical
  -- product c^(sum coefficients), and degree is zero
  sorry
```

These are SEAM2-scale grind lemmas: finite support, products, `zpow`, and `degree = 0`.

Named API:

```lean
Finset.prod
Finsupp.support
zpow
Units
Units.ext
Subgroup
```

---

### File D: `FLT/EllipticCurve/WeilPairing/MillerRecurrence.lean`

Goal: define `f_{n,P}` syntactically and prove its divisor.

Use the slow linear recurrence first. Do not optimize to double-and-add until everything works.

```lean
namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

namespace MillerExpr

noncomputable def addStepExpr
    (P Q : (E⁄K).Point) : E.MillerExpr :=
  .mul (.line P Q) (.inv (.vertical (P + Q)))

theorem divExpr_addStepExpr
    (P Q : (E⁄K).Point) :
    divExpr (E := E) (addStepExpr (E := E) P Q) =
      DivExpr.point (E := E) P +
      DivExpr.point (E := E) Q -
      DivExpr.point (E := E) (P + Q) -
      DivExpr.point (E := E) 0 := by
  -- from line and vertical divisor formulas
  sorry

noncomputable def millerNat
    (n : ℕ) (P : (E⁄K).Point) : E.MillerExpr :=
  match n with
  | 0 => .one
  | 1 => .one
  | n + 2 =>
      .mul (millerNat (E := E) (n + 1) P)
        (addStepExpr (E := E) ((n + 1 : ℕ) • P) P)

theorem divExpr_millerNat_succ
    (n : ℕ) (P : (E⁄K).Point) :
    divExpr (E := E) (millerNat (E := E) (n + 1) P) =
      (n + 1 : ℤ) • DivExpr.point (E := E) P
        - DivExpr.point (E := E) ((n + 1 : ℕ) • P)
        - (n : ℤ) • DivExpr.point (E := E) 0 := by
  induction n with
  | zero =>
      simp [millerNat]
  | succ n ih =>
      -- use `divExpr_addStepExpr` and additive algebra in `DivExpr`
      sorry

theorem divExpr_miller_torsion
    {m : ℕ} [NeZero m] (P : E.nTorsion m) :
    divExpr (E := E) (millerNat (E := E) m P.1) =
      (m : ℤ) • DivExpr.point (E := E) P.1
        - (m : ℤ) • DivExpr.point (E := E) 0 := by
  have hmpos : 0 < m := NeZero.pos m
  cases m with
  | zero => cases (NeZero.ne 0 rfl)
  | succ n =>
      have h := divExpr_millerNat_succ (E := E) n P.1
      -- use `P.property` to rewrite `(n+1) • P.1 = 0`
      simpa [Nat.succ_eq_add_one, hmpos.ne'] using h

end MillerExpr
end WeierstrassCurve
```

Named API:

```lean
Submodule.torsionBy
WeierstrassCurve.nTorsion
NeZero.pos
Nat.smul
zsmul
```

This file is manageable once the line/vertical divisor formulas exist.

---

### File E: `FLT/EllipticCurve/WeilPairing/Reciprocity.lean`

This is the first genuinely hard primitive.

Do **not** inline this into the package file. Expose the usable theorem:

```lean
namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

namespace MillerExpr

theorem weil_reciprocity_millerExpr
    (f g : E.MillerExpr)
    (hfg : Disjoint (divExpr (E := E) f).support (divExpr (E := E) g).support) :
    evalDiv (E := E) f (divExpr (E := E) g)
      (degree_divExpr (E := E) g) hfg =
    evalDiv (E := E) g (divExpr (E := E) f)
      (degree_divExpr (E := E) f) hfg.symm := by
  -- hard: tame symbols / product formula
  sorry

end MillerExpr
end WeierstrassCurve
```

Internally, this should eventually come from:

```lean
def tameSymbol
    (P : (E⁄K).Point) (f g : E.MillerExpr) : Kˣ := sorry

theorem product_tameSymbol_eq_one
    (f g : E.MillerExpr) :
    (∏ P in finiteBadSupport f g, tameSymbol (E := E) P f g) = 1 := by
  sorry

theorem weil_reciprocity_millerExpr_of_tame_symbols :
    ... := by
  sorry
```

This is **not** SEAM2.

---

### File F: `FLT/EllipticCurve/WeilPairing/Pairing.lean`

Goal: define the raw Miller-Weil value and prove the four mathematical properties.

Expose a base-field value:

```lean
namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
variable (m : ℕ) [NeZero m]

noncomputable def millerWeilValue
    (P Q : E.nTorsion m) : ℚˣ :=
  sorry
```

Then the required theorems:

```lean
theorem millerWeilValue_pow_eq_one
    (P Q : E.nTorsion m) :
    ((millerWeilValue (E := E) m P Q : ℚˣ) : ℚ) ^ m = 1 := by
  -- uses reciprocity with `div fP = m[P]-m[O]`
  sorry

theorem millerWeilValue_map_add_left
    (P P' Q : E.nTorsion m) :
    millerWeilValue (E := E) m (P + P') Q =
      millerWeilValue (E := E) m P Q *
      millerWeilValue (E := E) m P' Q := by
  -- uses divisor relation for f_{P+P'} versus fP*fP'*line^m
  sorry

theorem millerWeilValue_map_add_right
    (P Q Q' : E.nTorsion m) :
    millerWeilValue (E := E) m P (Q + Q') =
      millerWeilValue (E := E) m P Q *
      millerWeilValue (E := E) m P Q' := by
  sorry

theorem millerWeilValue_alternating
    (P : E.nTorsion m) :
    millerWeilValue (E := E) m P P = 1 := by
  sorry

theorem millerWeilValue_nondeg_left
    (P : E.nTorsion m)
    (hP : ∀ Q : E.nTorsion m,
      millerWeilValue (E := E) m P Q = 1) :
    P = 0 := by
  -- hard: nondegeneracy, normally via geometric pairing + card/cardinality
  sorry
```

Then build the subgroup-valued pairing:

```lean
noncomputable def rationalWeilPairing
    (P Q : E.nTorsion m) : rootsOfUnity m ℚ :=
  rootsOfUnity.mkOfPowEq
    ((millerWeilValue (E := E) m P Q : ℚˣ) : ℚ)
    (millerWeilValue_pow_eq_one (E := E) m P Q)

@[simp] theorem rationalWeilPairing_coe
    (P Q : E.nTorsion m) :
    (((rationalWeilPairing (E := E) m P Q : ℚˣ) : ℚ)) =
      ((millerWeilValue (E := E) m P Q : ℚˣ) : ℚ) := by
  simp [rationalWeilPairing, rootsOfUnity.coe_mkOfPowEq]
```

Bilinearity proofs should be done by coercing out of `rootsOfUnity`:

```lean
theorem rationalWeilPairing_map_add_left
    (P P' Q : E.nTorsion m) :
    rationalWeilPairing (E := E) m (P + P') Q =
      rationalWeilPairing (E := E) m P Q *
      rationalWeilPairing (E := E) m P' Q := by
  apply rootsOfUnity.coe_injective
  simp [rationalWeilPairing_coe, millerWeilValue_map_add_left]

theorem rationalWeilPairing_map_add_right
    (P Q Q' : E.nTorsion m) :
    rationalWeilPairing (E := E) m P (Q + Q') =
      rationalWeilPairing (E := E) m P Q *
      rationalWeilPairing (E := E) m P Q' := by
  apply rootsOfUnity.coe_injective
  simp [rationalWeilPairing_coe, millerWeilValue_map_add_right]

theorem rationalWeilPairing_alternating
    (P : E.nTorsion m) :
    rationalWeilPairing (E := E) m P P = 1 := by
  apply rootsOfUnity.coe_injective
  simp [rationalWeilPairing_coe, millerWeilValue_alternating]
```

Named Mathlib API:

```lean
rootsOfUnity
rootsOfUnity.mkOfPowEq
rootsOfUnity.coe_mkOfPowEq
rootsOfUnity.coe_injective
mem_rootsOfUnity
Units
Units.ext
Subgroup
```

---

### File G: `FLT/EllipticCurve/WeilPairing/FullGrid.lean`

This is the wrapper for `nondeg_left_on_full_grid`.

The key point: **a bare injection**

```lean
ZMod m × ZMod m ↪ (E⁄ℚ).Point
```

is not enough. You need the grid as an additive map into torsion, plus fullness/surjectivity onto the torsion group being tested.

Recommended API for `HasFullRationalTorsion`:

```lean
structure WeierstrassCurve.HasFullRationalTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
    (m : ℕ) where
  grid : (ZMod m × ZMod m) →+ (E⁄ℚ).Point
  grid_torsion : ∀ z : ZMod m × ZMod m, m • grid z = 0
  grid_injective : Function.Injective grid
  grid_full :
    Function.Surjective
      (fun z : ZMod m × ZMod m =>
        (⟨grid z, by
          simpa [WeierstrassCurve.nTorsion] using grid_torsion z⟩ : E.nTorsion m))
```

Then define the torsion-valued grid map:

```lean
namespace WeierstrassCurve.HasFullRationalTorsion

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] [DecidableEq ℚ]
variable {m : ℕ} (H : E.HasFullRationalTorsion m)

noncomputable def gridNTorsion :
    (ZMod m × ZMod m) →+ E.nTorsion m where
  toFun z :=
    ⟨H.grid z, by
      simpa [WeierstrassCurve.nTorsion] using H.grid_torsion z⟩
  map_zero' := by
    ext
    simp
  map_add' z w := by
    ext
    simp

theorem gridNTorsion_injective :
    Function.Injective H.gridNTorsion := by
  intro z w h
  apply H.grid_injective
  exact congrArg Subtype.val h

theorem gridNTorsion_surjective :
    Function.Surjective H.gridNTorsion := by
  simpa [gridNTorsion] using H.grid_full

end WeierstrassCurve.HasFullRationalTorsion
```

Now the exact nondegeneracy transfer lemma is tiny.

```lean
namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
variable (m : ℕ) [NeZero m]

theorem rationalWeilPairing_nondeg_left_on_full_grid
    (H : E.HasFullRationalTorsion m)
    (z : ZMod m × ZMod m)
    (hz : ∀ w : ZMod m × ZMod m,
      rationalWeilPairing (E := E) m
        (H.gridNTorsion z) (H.gridNTorsion w) = 1) :
    z = 0 := by
  have hzP : H.gridNTorsion z = 0 := by
    apply millerWeilValue_nondeg_left
    intro Q
    rcases H.gridNTorsion_surjective Q with ⟨w, rfl⟩
    -- after coercion or via the subgroup-valued nondeg theorem
    -- this should reduce to `hz w`
    exact by
      -- if `millerWeilValue_nondeg_left` is stated for `rationalWeilPairing`,
      -- this is exactly `hz w`
      sorry
  apply H.gridNTorsion_injective
  simpa using hzP

end WeierstrassCurve
```

Better: state the primitive nondegeneracy directly for the subgroup-valued pairing:

```lean
theorem rationalWeilPairing_nondeg_left
    (P : E.nTorsion m)
    (hP : ∀ Q : E.nTorsion m,
      rationalWeilPairing (E := E) m P Q = 1) :
    P = 0 := by
  sorry
```

Then the full-grid theorem has no coercion issue:

```lean
theorem rationalWeilPairing_nondeg_left_on_full_grid
    (H : E.HasFullRationalTorsion m)
    (z : ZMod m × ZMod m)
    (hz : ∀ w : ZMod m × ZMod m,
      rationalWeilPairing (E := E) m
        (H.gridNTorsion z) (H.gridNTorsion w) = 1) :
    z = 0 := by
  have hzP : H.gridNTorsion z = 0 := by
    apply rationalWeilPairing_nondeg_left
    intro Q
    rcases H.gridNTorsion_surjective Q with ⟨w, rfl⟩
    exact hz w
  apply H.gridNTorsion_injective
  simpa using hzP
```

That is the exact obligation.

If the nondegeneracy primitive is geometric, over `AlgebraicClosure ℚ`, use this shape instead:

```lean
theorem nondeg_left_on_full_grid_of_geometric_nondeg
    {EbarTors : Type*}
    [AddCommGroup EbarTors]
    (baseChangeTors : E.nTorsion m →+ EbarTors)
    (baseChangeTors_injective : Function.Injective baseChangeTors)
    (ebar : EbarTors → EbarTors → rootsOfUnity m (AlgebraicClosure ℚ))
    (embedRoots : rootsOfUnity m ℚ →* rootsOfUnity m (AlgebraicClosure ℚ))
    (compat :
      ∀ P Q : E.nTorsion m,
        embedRoots (rationalWeilPairing (E := E) m P Q) =
          ebar (baseChangeTors P) (baseChangeTors Q))
    (geom_nondeg :
      ∀ Pbar : EbarTors, (∀ Qbar : EbarTors, ebar Pbar Qbar = 1) → Pbar = 0)
    (H : E.HasFullRationalTorsion m)
    (Hfull_geom :
      Function.Surjective
        (fun z : ZMod m × ZMod m =>
          baseChangeTors (H.gridNTorsion z)))
    (z : ZMod m × ZMod m)
    (hz : ∀ w : ZMod m × ZMod m,
      rationalWeilPairing (E := E) m
        (H.gridNTorsion z) (H.gridNTorsion w) = 1) :
    z = 0 := by
  have hzbar : baseChangeTors (H.gridNTorsion z) = 0 := by
    apply geom_nondeg
    intro Qbar
    rcases Hfull_geom Qbar with ⟨w, rfl⟩
    rw [← compat]
    simp [hz w]
  have hzP : H.gridNTorsion z = 0 := by
    apply baseChangeTors_injective
    simpa using hzbar
  apply H.gridNTorsion_injective
  simpa using hzP
```

This is the mathematically honest version: geometric nondegeneracy plus a full rational grid surjecting onto geometric `m`-torsion.

---

### File H: `FLT/EllipticCurve/WeilPairing/Package.lean`

This file should be boring.

```lean
namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
variable (m : ℕ) [NeZero m]

noncomputable def rationalWeilPairingPackage :
    E.WeilPairingPackage m where
  pairing := rationalWeilPairing (E := E) m
  map_add_left := by
    intro P P' Q
    exact rationalWeilPairing_map_add_left (E := E) m P P' Q
  map_add_right := by
    intro P Q Q'
    exact rationalWeilPairing_map_add_right (E := E) m P Q Q'
  alternating := by
    intro P
    exact rationalWeilPairing_alternating (E := E) m P
  nondeg_left_on_full_grid := by
    intro H z hz
    exact rationalWeilPairing_nondeg_left_on_full_grid
      (E := E) (m := m) H z hz

end WeierstrassCurve
```

If your existing package field has a slightly different argument order, keep this exact proof shape and only reorder the binders.

---

## 2. The exact `nondeg_left_on_full_grid` obligation

The field should not be stated using only an injection into points. The usable statement is:

```lean
nondeg_left_on_full_grid :
  ∀ H : E.HasFullRationalTorsion m,
  ∀ z : ZMod m × ZMod m,
    (∀ w : ZMod m × ZMod m,
      pairing (H.gridNTorsion z) (H.gridNTorsion w) = 1) →
    z = 0
```

The proof is:

```lean
theorem nondeg_left_on_full_grid_of_nondeg_left
    {e : E.nTorsion m → E.nTorsion m → rootsOfUnity m ℚ}
    (hnd :
      ∀ P : E.nTorsion m,
        (∀ Q : E.nTorsion m, e P Q = 1) → P = 0)
    (H : E.HasFullRationalTorsion m)
    (z : ZMod m × ZMod m)
    (hz : ∀ w : ZMod m × ZMod m,
      e (H.gridNTorsion z) (H.gridNTorsion w) = 1) :
    z = 0 := by
  have hzP : H.gridNTorsion z = 0 := by
    apply hnd
    intro Q
    rcases H.gridNTorsion_surjective Q with ⟨w, rfl⟩
    exact hz w
  apply H.gridNTorsion_injective
  simpa using hzP
```

This proof uses exactly two `HasFullRationalTorsion` facts:

```lean
H.gridNTorsion_injective :
  Function.Injective H.gridNTorsion

H.gridNTorsion_surjective :
  Function.Surjective H.gridNTorsion
```

So if the current structure only stores

```lean
grid : ZMod m × ZMod m ↪ (E⁄ℚ).Point
```

then the structure is underspecified for this field. Add either:

```lean
grid_full :
  Function.Surjective H.gridNTorsion
```

or store the full grid directly as an additive equivalence:

```lean
gridEquiv : (ZMod m × ZMod m) ≃+ E.nTorsion m
```

The cleanest API is:

```lean
structure HasFullRationalTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
    (m : ℕ) where
  gridEquiv : (ZMod m × ZMod m) ≃+ E.nTorsion m
```

Then the proof becomes:

```lean
theorem nondeg_left_on_full_grid_of_nondeg_left'
    {e : E.nTorsion m → E.nTorsion m → rootsOfUnity m ℚ}
    (hnd :
      ∀ P : E.nTorsion m,
        (∀ Q : E.nTorsion m, e P Q = 1) → P = 0)
    (H : E.HasFullRationalTorsion m)
    (z : ZMod m × ZMod m)
    (hz : ∀ w : ZMod m × ZMod m,
      e (H.gridEquiv z) (H.gridEquiv w) = 1) :
    z = 0 := by
  have hzP : H.gridEquiv z = 0 := by
    apply hnd
    intro Q
    rcases H.gridEquiv.surjective Q with ⟨w, rfl⟩
    exact hz w
  exact H.gridEquiv.injective (by simpa using hzP)
```

That is the version I would prefer.

---

## 3. Hard primitives versus build-now scope

The genuinely hard primitives are these.

### Hard primitive 1: line/vertical divisor formulas

Even in the syntactic route, you need:

```lean
theorem divExpr_line :
    MillerExpr.divExpr (E := E) (.line P Q) =
      DivExpr.point (E := E) P +
      DivExpr.point (E := E) Q +
      DivExpr.point (E := E) (-(P + Q)) -
      3 • DivExpr.point (E := E) 0 := by
  sorry

theorem divExpr_vertical :
    MillerExpr.divExpr (E := E) (.vertical P) =
      DivExpr.point (E := E) P +
      DivExpr.point (E := E) (-P) -
      2 • DivExpr.point (E := E) 0 := by
  sorry
```

You said `xRep_add` is already designed elsewhere; then these should be treated as the local coordinate/divisor seam and imported.

### Hard primitive 2: Weil reciprocity for `MillerExpr`

The useful exported theorem should be:

```lean
theorem weil_reciprocity_millerExpr
    (f g : E.MillerExpr)
    (hfg : Disjoint (MillerExpr.divExpr (E := E) f).support
                    (MillerExpr.divExpr (E := E) g).support) :
    MillerExpr.evalDiv (E := E) f (MillerExpr.divExpr (E := E) g)
      (MillerExpr.degree_divExpr (E := E) g) hfg =
    MillerExpr.evalDiv (E := E) g (MillerExpr.divExpr (E := E) f)
      (MillerExpr.degree_divExpr (E := E) f) hfg.symm := by
  sorry
```

Internally this is tame symbols and a product formula. This is not a local `simp` grind.

### Hard primitive 3: nondegeneracy

The exported theorem should be either rational:

```lean
theorem rationalWeilPairing_nondeg_left
    (P : E.nTorsion m)
    (hP : ∀ Q : E.nTorsion m,
      rationalWeilPairing (E := E) m P Q = 1) :
    P = 0 := by
  sorry
```

or geometric plus base-change compatibility:

```lean
theorem geometricWeilPairing_nondeg_left :
    ∀ P : Ebar.nTorsion m,
      (∀ Q : Ebar.nTorsion m, ebar P Q = 1) → P = 0 := by
  sorry
```

together with:

```lean
theorem rationalWeilPairing_baseChange :
    ∀ P Q : E.nTorsion m,
      embedRoots (rationalWeilPairing (E := E) m P Q) =
        geometricWeilPairing (baseChangeTors P) (baseChangeTors Q) := by
  sorry
```

and grid fullness after base change.

The card argument is a serious theorem: it uses the size of full `m`-torsion, the size/cyclicity of `rootsOfUnity m`, and the annihilator/radical argument for a bilinear alternating pairing.

---

## Honest scope verdict

The full Miller construction is **not** a SEAM2-scale grind. It is multi-week infrastructure unless the project already has:

```lean
Divisor / principal divisor API on Weierstrass curves
evaluation of rational functions on divisors
tame symbols
Weil reciprocity
line/vertical divisor formulas
geometric torsion cardinality and base-change compatibility
```

For the current A2 residual seam, I would leave the Miller construction as named seams and immediately discharge the package using the wrapper layer.

The first concrete lemma I would dispatch now is the full-grid transfer:

```lean
theorem nondeg_left_on_full_grid_of_nondeg_left
    {e : E.nTorsion m → E.nTorsion m → rootsOfUnity m ℚ}
    (hnd :
      ∀ P : E.nTorsion m,
        (∀ Q : E.nTorsion m, e P Q = 1) → P = 0)
    (H : E.HasFullRationalTorsion m)
    (z : ZMod m × ZMod m)
    (hz : ∀ w : ZMod m × ZMod m,
      e (H.gridNTorsion z) (H.gridNTorsion w) = 1) :
    z = 0 := by
  have hzP : H.gridNTorsion z = 0 := by
    apply hnd
    intro Q
    rcases H.gridNTorsion_surjective Q with ⟨w, rfl⟩
    exact hz w
  apply H.gridNTorsion_injective
  simpa using hzP
```

Then `rationalWeilPairingPackage` should be a shallow constructor:

```lean
noncomputable def rationalWeilPairingPackage
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]
    (m : ℕ) [NeZero m] :
    E.WeilPairingPackage m where
  pairing := rationalWeilPairing (E := E) m
  map_add_left := rationalWeilPairing_map_add_left (E := E) m
  map_add_right := rationalWeilPairing_map_add_right (E := E) m
  alternating := rationalWeilPairing_alternating (E := E) m
  nondeg_left_on_full_grid :=
    rationalWeilPairing_nondeg_left_on_full_grid (E := E) (m := m)
```

If the package currently has no `[NeZero m]`, add it or make the constructor require `hm : m ≠ 0`; the `rootsOfUnity.mkOfPowEq` path is much cleaner with `[NeZero m]`.
