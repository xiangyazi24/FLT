
═══ BRIDGE SUBMITTED  dm4 | task bd9fe7db | 1832B in | "Q8 (dm4): Lean 4 / Mathlib. flt-ai. SCOPING the deepest pill…" ═══

[ask-gpt dm4 tid=bd9fe7db +0s] dispatched, waiting for answer
[ask-gpt dm4 tid=bd9fe7db +90s] waiting (status=processing)
[ask-gpt dm4 tid=bd9fe7db +180s] waiting (status=processing)
[ask-gpt dm4 tid=bd9fe7db +270s] waiting (status=processing)
[ask-gpt dm4 tid=bd9fe7db +360s] waiting (status=processing)
[ask-gpt dm4 tid=bd9fe7db +450s] waiting (status=processing)
[ask-gpt dm4 tid=bd9fe7db +540s] waiting (status=processing)
[ask-gpt dm4 tid=bd9fe7db +610s] terminal: status=completed

═══ BRIDGE RUN #38  dm4 | task bd9fe7db | 18773 B | ✅ COMPLETE ═══

## Verdict

`mordell_weil_fg` should remain a **named deep pillar**. Current Mathlib has a surprisingly useful **abstract descent + height substrate**, but it does **not** currently have a Mordell-Weil theorem, weak Mordell-Weil/Selmer machinery, or a finished elliptic-curve point-height package. I would scope full Mordell-Weil as a research-level formalization effort, not a local `flt-ai` seam discharge.

The best near-term replacement strategy is **not** full MW. Since your actual downstream need is only rational torsion finiteness, the cheaper path is likely a **height-based torsion-finiteness theorem** once the point-height API is completed, or a **good-reduction torsion-injection theorem** if point reduction/formal-group infrastructure is built. Of those two, the height route looks more aligned with Mathlib’s current state.

---

## 1. What Mathlib currently has

### A. Elliptic curves and rational point groups

Mathlib has the affine nonsingular point type and the group law:

```lean
(E⁄K).Point
```

with an additive commutative group structure. The relevant module is:

```lean
Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
```

Important API already present includes:

```lean
WeierstrassCurve.Affine.Point
WeierstrassCurve.Affine.Point.instAddCommGroup
WeierstrassCurve.Affine.Point.map
WeierstrassCurve.Affine.Point.map_zero
WeierstrassCurve.Affine.Point.map_id
WeierstrassCurve.Affine.Point.map_map
WeierstrassCurve.Affine.Point.xRep
WeierstrassCurve.Affine.CoordinateRing
WeierstrassCurve.Affine.FunctionField
```

The docs explicitly describe the affine point group law and its construction through the coordinate ring and ideal class group calculations, so this is real infrastructure, not merely definitions. citeturn562701view0

Mathlib also has elliptic-curve division polynomial modules:

```lean
Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
```

with names such as:

```lean
WeierstrassCurve.preΨ
WeierstrassCurve.ΨSq
WeierstrassCurve.Ψ
WeierstrassCurve.Φ
WeierstrassCurve.ψ
WeierstrassCurve.φ
```

This is relevant for fixed-`n` torsion, but it is not by itself a proof that the full rational torsion subgroup is finite. citeturn952027view0turn952027view1

Mathlib has curve-level reduction infrastructure:

```lean
Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
```

including integral/minimal models, reduction of a Weierstrass curve, and good/multiplicative/additive reduction predicates:

```lean
WeierstrassCurve.IsIntegral
WeierstrassCurve.IsMinimal
WeierstrassCurve.minimal
WeierstrassCurve.reduction
WeierstrassCurve.HasGoodReduction
WeierstrassCurve.HasMultiplicativeReduction
WeierstrassCurve.HasAdditiveReduction
```

But this is currently much closer to **model/reduction theory** than to the full point-reduction/formal-group theorem needed for torsion injection. citeturn406854view1

---

### B. Mordell-Weil itself

I do **not** see an exported Mathlib theorem/module named around “Mordell”; the all-import docs search has no `Mordell` match. So the theorem

```lean
theorem mordell_weil_fg
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    AddGroup.FG (E⁄ℚ).Point := ...
```

does not appear to be present under a recognizable Mordell-Weil name. citeturn720701view0

Nor do I see weak Mordell-Weil machinery under names like `Selmer`, `MordellWeil`, or elliptic Kummer maps. Mathlib does have a field-theoretic Kummer extension file,

```lean
Mathlib.FieldTheory.KummerExtension
```

but that is about cyclic/Kummer field extensions and automorphisms of roots of unity, not the elliptic-curve Kummer sequence/Selmer group package required for weak Mordell-Weil. citeturn177269view0turn177269view3

---

### C. Heights

Mathlib has a substantial general height stack:

```lean
Mathlib.NumberTheory.Height.Basic
Mathlib.NumberTheory.Height.NumberField
Mathlib.NumberTheory.Height.Projectivization
Mathlib.NumberTheory.Height.Northcott
Mathlib.NumberTheory.Height.EllipticCurve
```

The base API includes:

```lean
Height.AdmissibleAbsValues
Height.mulHeight₁
Height.logHeight₁
Height.mulHeight
Height.logHeight
Height.Finsupp.mulHeight
Height.Finsupp.logHeight
```

and the number-field/rational specialization includes:

```lean
NumberField.instAdmissibleAbsValues
Rat.mulHeight_eq_max_abs_of_gcd_eq_one
Rat.logHeight_eq_max_abs_of_gcd_eq_one
Rat.mulHeight₁_eq_max
Rat.logHeight₁_eq_log_max
```

So the global height foundation is present. citeturn720701view1turn191982view0turn217970view2

There is also an elliptic-curve height file:

```lean
Mathlib.NumberTheory.Height.EllipticCurve
```

but it is not yet a finished Mordell-Weil height theory. The key exported theorem is an approximate height bound for the polynomial `addSubMap`; the file’s own TODO list says to define the naïve height and add the ingredients for the approximate parallelogram law. citeturn217970view0

The theorem Mathlib already has is essentially of this shape:

```lean
theorem WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le
    {K : Type u} [Field K] [Height.AdmissibleAbsValues K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ C : ℝ, ∀ x : Fin 3 → K,
      |Height.logHeight
          (fun i => MvPolynomial.eval x (W.addSubMap i))
        - 2 * Height.logHeight x| ≤ C
```

This is promising, but it is not yet the point-level theorem needed for Mordell-Weil.

---

### D. Abstract descent theorem

This is the most important good news. Mathlib already has the **abstract descent theorem**:

```lean
Mathlib.GroupTheory.Descent
```

The docs explicitly say that this proves finite generation from finite index of multiplication-by-`2` plus a height satisfying an approximate parallelogram law, and that it is one of the main ingredients in the standard proof of Mordell-Weil. citeturn424067view2

The key theorem is:

```lean
AddCommGroup.fg_of_descent'
```

Conceptually:

```lean
theorem AddCommGroup.fg_of_descent'
    {G : Type*} [AddCommGroup G]
    {h : G → ℝ} {C : ℝ}
    (H₁ : (nsmulAddMonoidHom 2 : G →+ G).range.FiniteIndex)
    (H₂ : ∀ x : G, 0 ≤ h x)
    (H₃ : ∀ x y : G,
      |h (x + y) + h (x - y) - 2 * (h x + h y)| ≤ C)
    [Northcott h] :
    AddGroup.FG G
```

So the Lean proof of Mordell-Weil, once the two big ingredients exist, should be a shallow wrapper.

---

### E. Number-field finiteness substrate

Mathlib has serious number-field finiteness infrastructure:

```lean
Mathlib.NumberTheory.ClassNumber.Finite
Mathlib.NumberTheory.NumberField.ClassNumber
Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
```

Relevant API includes:

```lean
ClassGroup.fintypeOfAdmissibleOfAlgebraic
ClassGroup.fintypeOfAdmissibleOfFinite
NumberField.RingOfIntegers.instFintypeClassGroup
NumberField.classNumber
NumberField.Units.rank
NumberField.Units.fundSystem
NumberField.Units.basisModTorsion
NumberField.Units.rank_modTorsion
NumberField.Units.instFGUnitsRingOfIntegers
```

So class group finiteness and Dirichlet’s unit theorem are present. citeturn217970view3turn406854view0turn609990view0

But this is only the number-theory substrate. Weak Mordell-Weil still needs the elliptic Kummer/Selmer bridge.

---

## 2. The standard MW route in Lean

The clean Lean target should not be “prove Mordell-Weil directly.” It should be:

```lean
namespace WeierstrassCurve

noncomputable def naivePointHeight
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point → ℝ :=
  sorry
```

Then prove four obligations:

```lean
theorem weakMW_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ((nsmulAddMonoidHom 2 :
      (E⁄ℚ).Point →+ (E⁄ℚ).Point).range).FiniteIndex :=
  sorry

theorem naivePointHeight_northcott
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Northcott (naivePointHeight E) :=
  sorry

theorem naivePointHeight_nonneg
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ P : (E⁄ℚ).Point, 0 ≤ naivePointHeight E P :=
  sorry

theorem naivePointHeight_parallelogram
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, ∀ P Q : (E⁄ℚ).Point,
      |naivePointHeight E (P + Q) +
        naivePointHeight E (P - Q) -
        2 * (naivePointHeight E P + naivePointHeight E Q)| ≤ C :=
  sorry
```

Then the final theorem is almost mechanical:

```lean
theorem mordell_weil_fg_of_weakMW_two_and_height
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hfinite :
      ((nsmulAddMonoidHom 2 :
        (E⁄ℚ).Point →+ (E⁄ℚ).Point).range).FiniteIndex)
    [Northcott (naivePointHeight E)]
    (hnonneg :
      ∀ P : (E⁄ℚ).Point, 0 ≤ naivePointHeight E P)
    (hpar :
      ∃ C : ℝ, ∀ P Q : (E⁄ℚ).Point,
        |naivePointHeight E (P + Q) +
          naivePointHeight E (P - Q) -
          2 * (naivePointHeight E P + naivePointHeight E Q)| ≤ C) :
    AddGroup.FG (E⁄ℚ).Point := by
  rcases hpar with ⟨C, hC⟩
  exact AddCommGroup.fg_of_descent'
    (G := (E⁄ℚ).Point)
    (h := naivePointHeight E)
    (C := C)
    hfinite
    hnonneg
    hC
```

This is the route Mathlib is clearly set up to support. Notice that **canonical/Néron-Tate height is not strictly necessary** for this proof shape. The abstract theorem uses a naïve height plus approximate parallelogram law.

---

## 3. Biggest missing component

For full Mordell-Weil, the biggest missing component is:

```lean
weakMW_two :
  ((nsmulAddMonoidHom 2 :
    (E⁄ℚ).Point →+ (E⁄ℚ).Point).range).FiniteIndex
```

or more generally:

```lean
weakMW_m :
  ((nsmulAddMonoidHom m :
    (E⁄ℚ).Point →+ (E⁄ℚ).Point).range).FiniteIndex
```

The height side is incomplete, but Mathlib already has:

```lean
Height.AdmissibleAbsValues
Height.logHeight
Height.Projectivization
Height.EllipticCurve.addSubMap bound
Northcott
AddCommGroup.fg_of_descent'
```

so the **shape** of the height/descent proof is already present. By contrast, weak Mordell-Weil needs new arithmetic geometry: elliptic Kummer maps, Selmer groups, finiteness of relevant local/global images, ramification control, and the bridge from class group/S-unit finiteness to finite Selmer sets.

Mathlib’s class group and unit theorem files are very helpful, but they do not make weak Mordell-Weil a short proof. They are ingredients underneath the proof, not the elliptic descent itself.

A plausible dependency tree for weak MW over `ℚ` is:

```lean
-- algebraic/arithmetic base
NumberField
NumberField.RingOfIntegers
ClassGroup
NumberField.classNumber
NumberField.Units
NumberField.Units.DirichletTheorem

-- elliptic descent layer, mostly missing
E.nTorsion m
E[m] as finite Galois module
Kummer map
Selmer group
local Kummer maps
finite support / unramified outside S
finite Selmer group

-- conclusion
weakMW_m :
  ((nsmulAddMonoidHom m :
    (E⁄ℚ).Point →+ (E⁄ℚ).Point).range).FiniteIndex
```

For a restricted 2-descent over `ℚ`, one can avoid some general Galois cohomology by using explicit maps to squareclasses, especially under extra hypotheses such as full rational 2-torsion. But for arbitrary `E/ℚ`, even 2-descent still needs a serious amount of new formalized arithmetic.

---

## 4. Scale estimate and realistic first steps

Full

```lean
mordell_weil_fg
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    AddGroup.FG (E⁄ℚ).Point
```

is not a “few-month focused project on top of Mathlib” unless several experts are simultaneously building the missing descent and height infrastructure. I would scope it as a **research-level formalization effort**.

A much more realistic first theorem is the wrapper theorem above:

```lean
theorem mordell_weil_fg_of_weakMW_two_and_height
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hfinite :
      ((nsmulAddMonoidHom 2 :
        (E⁄ℚ).Point →+ (E⁄ℚ).Point).range).FiniteIndex)
    [Northcott (naivePointHeight E)]
    (hnonneg :
      ∀ P : (E⁄ℚ).Point, 0 ≤ naivePointHeight E P)
    (hpar :
      ∃ C : ℝ, ∀ P Q : (E⁄ℚ).Point,
        |naivePointHeight E (P + Q) +
          naivePointHeight E (P - Q) -
          2 * (naivePointHeight E P + naivePointHeight E Q)| ≤ C) :
    AddGroup.FG (E⁄ℚ).Point := by
  rcases hpar with ⟨C, hC⟩
  exact AddCommGroup.fg_of_descent'
    (G := (E⁄ℚ).Point)
    (h := naivePointHeight E)
    (C := C)
    hfinite
    hnonneg
    hC
```

That theorem is a genuine integration point and should be easy once the names line up.

The next real height-side milestone is:

```lean
theorem naivePointHeight_parallelogram
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, ∀ P Q : (E⁄ℚ).Point,
      |naivePointHeight E (P + Q) +
        naivePointHeight E (P - Q) -
        2 * (naivePointHeight E P + naivePointHeight E Q)| ≤ C :=
  sorry
```

This is likely a focused project, because `Mathlib.NumberTheory.Height.EllipticCurve` already proves the polynomial-map height estimate that is supposed to feed this result. But it still requires defining the point height, connecting affine/projective coordinates, handling `0`, and proving the relevant Northcott instance.

A descent-side first milestone would be a deliberately restricted weak Mordell-Weil theorem, for example full rational 2-torsion:

```lean
theorem weakMW_two_of_full_rational_two_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h2 : E.HasFullRationalTorsion 2) :
    ((nsmulAddMonoidHom 2 :
      (E⁄ℚ).Point →+ (E⁄ℚ).Point).range).FiniteIndex :=
  sorry
```

Even this is not small, but it is much more concrete than arbitrary Selmer theory.

---

## 5. Weaker target: torsion finiteness

Since your downstream need is only:

```lean
Finite (AddCommMonoid.addTorsion (E⁄ℚ).Point)
```

or an equivalent torsion-finiteness statement, proving full Mordell-Weil is overkill.

There are three plausible routes.

---

### Route T1: derive torsion finiteness from full MW

This is the current route:

```lean
theorem rational_torsion_finite_of_mordell_weil
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hMW : AddGroup.FG (E⁄ℚ).Point) :
    (AddCommMonoid.addTorsion (E⁄ℚ).Point).Finite :=
  sorry
```

This is algebraically clean, but it imports the whole Mordell-Weil theorem.

---

### Route T2: good reduction injection

The classical cheaper arithmetic route is:

1. choose good primes `p`, `q`;
2. define point reduction maps;
3. prove injectivity on prime-to-`p` torsion;
4. use two good primes to control all torsion;
5. conclude torsion embeds into a finite product of finite groups over finite fields.

The Lean target would look like:

```lean
noncomputable def reductionOnPoints
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) :
    (E⁄ℚ).Point →+ sorry :=
  sorry

theorem reductionOnPoints_injective_on_prime_to_p_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p n : ℕ}
    (hp : Nat.Prime p)
    (hgood : sorry) -- good reduction at p
    (hcop : Nat.Coprime n p) :
    Function.Injective
      (fun P : E.nTorsion n =>
        reductionOnPoints E p P.1) :=
  sorry
```

This is strictly weaker than Mordell-Weil, but it still needs deep local infrastructure: point reduction, integral coordinates for rational points at good primes, finite-field point groups, kernel of reduction, and the formal-group or local argument that the reduction kernel has no prime-to-`p` torsion.

Mathlib has curve-level reduction predicates, but I would not treat this as currently ready-to-discharge. citeturn406854view1

---

### Route T3: height-based torsion finiteness

This may be the cheapest route relative to current Mathlib. It avoids weak Mordell-Weil entirely.

The idea: prove a point-height double inequality and use Northcott. A torsion point has bounded height, and a Northcott height has only finitely many points below any bound.

A useful abstract lemma would be:

```lean
theorem finite_torsion_of_northcott_double
    {G : Type*} [AddCommGroup G]
    (h : G → ℝ)
    [Northcott h]
    (h_nonneg : ∀ x : G, 0 ≤ h x)
    (h_double :
      ∃ C : ℝ, ∀ x : G,
        h (2 • x) ≥ 4 * h x - C) :
    (AddCommMonoid.addTorsion G).Finite :=
  sorry
```

Then the elliptic-curve application would be:

```lean
theorem rational_torsion_finite_of_height
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [Northcott (naivePointHeight E)]
    (h_nonneg :
      ∀ P : (E⁄ℚ).Point, 0 ≤ naivePointHeight E P)
    (h_double :
      ∃ C : ℝ, ∀ P : (E⁄ℚ).Point,
        naivePointHeight E (2 • P) ≥
          4 * naivePointHeight E P - C) :
    (AddCommMonoid.addTorsion (E⁄ℚ).Point).Finite :=
  finite_torsion_of_northcott_double
    (G := (E⁄ℚ).Point)
    (h := naivePointHeight E)
    h_nonneg
    h_double
```

This route needs less arithmetic geometry than good-reduction torsion injection and much less than weak Mordell-Weil. It still needs the point-height API, but that is aligned with existing Mathlib height work.

The abstract torsion-height lemma is probably the smallest genuinely useful first step. It is independent of elliptic curves and can be proved in pure group/height language using `Northcott`.

---

## 6. Fixed-`n` torsion finiteness is also a useful subgoal

Another smaller target is:

```lean
theorem nTorsion_finite_rat
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} (hn : 0 < n) :
    Finite (E.nTorsion n) :=
  sorry
```

or, without the abbreviation:

```lean
theorem torsionBy_finite_rat
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} (hn : 0 < n) :
    Finite (Submodule.torsionBy ℤ (E⁄ℚ).Point n) :=
  sorry
```

This should eventually follow from division polynomials: nonzero `n`-torsion points have coordinates satisfying division-polynomial equations, hence finitely many possibilities. Mathlib’s division polynomial files are the right starting point, but the connection between those polynomials and the kernel of multiplication-by-`n` on the point group is the missing theorem. citeturn952027view0turn952027view1

This proves only bounded-exponent torsion. It does **not** prove the whole torsion subgroup finite unless one also proves a bound on possible rational torsion orders.

---

## Recommendation for `flt-ai`

Keep:

```lean
axiom mordell_weil_fg
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    AddGroup.FG (E⁄ℚ).Point
```

as a deep named pillar.

But introduce a weaker named seam for the actual downstream need:

```lean
axiom rational_torsion_finite
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommMonoid.addTorsion (E⁄ℚ).Point).Finite
```

Then, separately add the bridge theorem:

```lean
theorem rational_torsion_finite_of_mordell_weil
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hMW : AddGroup.FG (E⁄ℚ).Point) :
    (AddCommMonoid.addTorsion (E⁄ℚ).Point).Finite :=
  sorry
```

Long-term, try to replace `rational_torsion_finite` by the height route first:

```lean
finite_torsion_of_northcott_double
```

then by an elliptic point-height double inequality. That is much smaller than full weak Mordell-Weil and avoids the Selmer/Kummer layer entirely.
