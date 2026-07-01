# Q3005 (dm-codex1): best N10 axiom-reduction split

Goal: replace

```lean
axiom kubert_C10_square
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta10 t ≠ 0 ∧ s ^ 2 = A10 t ^ 2 - 4 * B10 t
```

by smaller components.

The best next split is:

1. **Checked/generic group extraction** from `ZMod 2 × ZMod 10`:
   exact-order-10 point plus full rational two-torsion data.
2. **Residual A10-normal-form only**:
   arbitrary elliptic curve with an order-10 point is variable-change equivalent to `tateW b c` with origin of order 10.
3. **Checked/soon-checked Tate row**:
   `hOriginOrder10 → c≠0`, `b-c≠0`, `tateC10_K=0`, then `tateC10_param_of_K` gives `t`.
4. **Residual Tate-to-short conversion only**, if too long:
   `tateW (tateC10_b t) (tateC10_c t)` is variable-change equivalent to `shortW (A10 t) (B10 t)` and `Delta10 t≠0`.
5. **Checked/generic short-model square lemma**:
   full rational two-torsion on `shortW A B` gives `∃ s, s²=A²-4B`.

This replaces the old global axiom by at most two narrow residuals:

```lean
axiom tate_normal_form_at_point_of_addOrder10
axiom tateC10_param_to_shortW
```

and after the current `P2+P3=5P` coordinate proof lands, the first residual is the main remaining one.

---

## 1. Generic group extraction from `ZMod 2 × ZMod 10`

Add a small structure if N12 does not already have one.  If N12 has `FullRationalTwoTorsion`, reuse that exact structure instead.

```lean
structure FullTwoTorsionData (G : Type*) [AddCommGroup G] where
  T₁ : G
  T₂ : G
  T₃ : G
  hT₁_two : (2 : ℕ) • T₁ = 0
  hT₂_two : (2 : ℕ) • T₂ = 0
  hT₃_two : (2 : ℕ) • T₃ = 0
  hT₁_ne_zero : T₁ ≠ 0
  hT₂_ne_zero : T₂ ≠ 0
  hT₃_ne_zero : T₃ ≠ 0
  hT₁_ne_T₂ : T₁ ≠ T₂
  hT₁_ne_T₃ : T₁ ≠ T₃
  hT₂_ne_T₃ : T₂ ≠ T₃

structure C10GroupData (G : Type*) [AddCommGroup G] where
  P : G
  hP_order : addOrderOf P = 10
  fullTwo : FullTwoTorsionData G
```

Recommended theorem statement:

```lean
theorem C10GroupData.of_injective_zmod2_prod_zmod10
    {G : Type*} [AddCommGroup G]
    (f : (ZMod 2 × ZMod 10) →+ G) (hf : Function.Injective f) :
    C10GroupData G := by
  refine
    { P := f (0, 1)
      hP_order := ?_
      fullTwo := ?_ }
  · -- Generic exact-order preservation under injective hom.
    -- Search N12 for the exact lemma name. Likely candidates:
    --   addOrderOf_map_eq_of_injective
    --   AddMonoidHom.addOrderOf_map_eq_of_injective
    --   orderOf_map_eq_of_injective
    simpa using addOrderOf_map_eq_of_injective f hf (0, 1)
  · refine
      { T₁ := f (1, 0)
        T₂ := f (0, 5)
        T₃ := f (1, 5)
        hT₁_two := ?_
        hT₂_two := ?_
        hT₃_two := ?_
        hT₁_ne_zero := ?_
        hT₂_ne_zero := ?_
        hT₃_ne_zero := ?_
        hT₁_ne_T₂ := ?_
        hT₁_ne_T₃ := ?_
        hT₂_ne_T₃ := ?_ }
    all_goals
      -- Use `map_nsmul`, `hf`, and `norm_num` in `ZMod`.
      -- If needed, prove these as one-line local lemmas first:
      --   by intro h; apply_fun (fun x => ?) at h
      -- Easier pattern:
      --   intro h; exact by simpa using hf h
      try simp [map_nsmul]
```

If the exact order preservation lemma is missing, prove a local generic lemma:

```lean
theorem addOrderOf_map_eq_of_injective
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Injective f) (x : A) :
    addOrderOf (f x) = addOrderOf x := by
  -- Search N12 first; this is standard and may already exist.
  -- Proof route: `addOrderOf_eq_iff` or `orderOf_map_eq_of_injective` after `toMultiplicative`.
  exact AddMonoidHom.addOrderOf_of_injective f hf x
```

The three order-two elements are `(1,0)`, `(0,5)`, `(1,5)`.  They are distinct and nonzero by `norm_num` in `ZMod 2 × ZMod 10` and injectivity.

---

## 2. Order-10 Tate normal form residual

Define the N10 analogue of the N12 structure:

```lean
structure TateNormalFormAtOrder10 (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  b : ℚ
  c : ℚ
  hb : b ≠ 0
  hDelta : (tateW b c).Δ ≠ 0
  C : WeierstrassCurve.VariableChange ℚ
  hCurve : C • E = tateW b c
  hOriginOrder : addOrderOf (tateOriginAffine b c hb) = 10
```

Small residual statement:

```lean
axiom tate_normal_form_at_point_of_addOrder10
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 10) :
    TateNormalFormAtOrder10 E
```

### Can N12 normal-form construction be generalized?

Yes, mostly.  The variable-change construction itself is not order-12-specific:

```text
extract affine point
translate to origin
kill a₄
scale to Tate form
transport order through additive equivalences
```

The order value is used only to discharge nondegeneracy lemmas.  For N10 replace the N12-specific nonzero lemmas by:

```lean
theorem origin_a3_ne_zero_of_addOrderOf_eq_10
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hO : (W⁄ℚ).Nonsingular 0 0)
    (hOrd : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 10) :
    W.a₃ ≠ 0 := by
  intro h3
  -- If a₃=0, `(0,0)` is 2-torsion, contradicting order 10.
  have h2 : (2 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 hO = 0 := by
    exact origin_two_nsmul_eq_zero_of_a3_eq_zero (W := W) hO h3
  have hdiv : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) ∣ 2 := by
    exact addOrderOf_dvd_of_nsmul_eq_zero h2
  rw [hOrd] at hdiv
  norm_num at hdiv

theorem origin_a2_ne_zero_of_addOrderOf_eq_10_of_a4_a6
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hO : (W⁄ℚ).Nonsingular 0 0)
    (hOrd : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 10)
    (hA4 : W.a₄ = 0) (hA6 : W.a₆ = 0) :
    W.a₂ ≠ 0 := by
  intro h2coeff
  -- With a₂=a₄=a₆=0 and a₃≠0, tangent doubling gives `2O=-O`, hence `3O=0`.
  have h3coeff : W.a₃ ≠ 0 :=
    origin_a3_ne_zero_of_addOrderOf_eq_10 (W := W) hO hOrd
  have h3tors : (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 hO = 0 := by
    exact origin_three_nsmul_eq_zero_of_a2_a4_a6_eq_zero
      (W := W) hO h2coeff hA4 hA6 h3coeff
  have hdiv : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) ∣ 3 := by
    exact addOrderOf_dvd_of_nsmul_eq_zero h3tors
  rw [hOrd] at hdiv
  norm_num at hdiv
```

Then the checked N12 assembly theorem should copy with `12` changed to `10`:

```lean
theorem tate_normal_form_at_point_of_addOrder10_checked
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 10) :
    TateNormalFormAtOrder10 E := by
  -- Same body as `tate_normal_form_at_point_of_addOrder12_checked`:
  --   affineMarkedPointOfOrderN/of_addOrder
  --   translatePointToOriginVC
  --   killA4VC
  --   scaleToTateVC
  --   tateW_delta_ne_zero_of_variableChange_eq
  --   order transport through affinePointAddEquivOfVariableChange
  -- Only the two nonzero lemmas above change.
  exact tate_normal_form_at_point_of_addOrder10_residual E P hP
```

If you do not want this whole construction in N10 yet, keep the `tate_normal_form_at_point_of_addOrder10` axiom as residual A.  It is much smaller than `kubert_C10_square` because it says nothing about full 2-torsion or the short obstruction.

---

## 3. Tate row consequences for exact order 10

These are the local N10 theorem statements to aim for.  You already have most of the algebra.

```lean
theorem tateC10_c_ne_zero_of_origin_order10
    {b c : ℚ} (hb : b ≠ 0)
    (hOrd : addOrderOf (tateOriginAffine b c hb) = 10) :
    c ≠ 0 := by
  intro hc
  -- If c=0, the Tate table degenerates to order dividing 4/5 depending on the local branch.
  -- Prove by explicit multiples, as in N12 `tate_c_ne_zero_of_origin_order12`.
  exact tateC10_c_ne_zero_of_origin_order10_residual hb hOrd hc

theorem tateC10_b_sub_c_ne_zero_of_origin_order10
    {b c : ℚ} (hb : b ≠ 0)
    (hOrd : addOrderOf (tateOriginAffine b c hb) = 10) :
    b - c ≠ 0 := by
  intro hbc
  -- If b=c, then 5P=0, so addOrderOf P ∣ 5, contradiction to 10.
  have h5 : (5 : ℕ) • tateOriginAffine b c hb = 0 := by
    exact tateOrigin_five_nsmul_eq_zero_of_b_eq_c (b := b) (c := c) hb (sub_eq_zero.mp hbc)
  have hdiv : addOrderOf (tateOriginAffine b c hb) ∣ 5 := by
    exact addOrderOf_dvd_of_nsmul_eq_zero h5
  rw [hOrd] at hdiv
  norm_num at hdiv

theorem tateC10_K_eq_zero_of_origin_order10
    {b c : ℚ} (hb : b ≠ 0)
    (hOrd : addOrderOf (tateOriginAffine b c hb) = 10) :
    tateC10_K b c = 0 := by
  have hbc : b - c ≠ 0 :=
    tateC10_b_sub_c_ne_zero_of_origin_order10 (b := b) (c := c) hb hOrd
  rcases tateC10_5P_eq (b := b) (c := c) hb hbc with ⟨h5, h5eq⟩
  have h10 : (10 : ℕ) • tateOriginAffine b c hb = 0 := by
    have h := addOrderOf_nsmul_eq_zero (tateOriginAffine b c hb)
    simpa [hOrd] using h
  have htwo_five :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some
        (tateC10_5P_x b c) (tateC10_5P_y b c) h5 = 0 := by
    rw [← h5eq]
    simpa [nsmul_nsmul, mul_comm, mul_left_comm, mul_assoc] using h10
  have hpsi :
      tateC10Psi2 b c (tateC10_5P_x b c) (tateC10_5P_y b c) = 0 :=
    tateC10Psi2_eq_zero_of_two_nsmul_eq_zero
      (b := b) (c := c)
      (x := tateC10_5P_x b c) (y := tateC10_5P_y b c)
      (hxy := h5) htwo_five
  have hrel := tateC10_psi2_5P_eq_K_div (b := b) (c := c) hb hbc
  rw [hpsi] at hrel
  have hbc3 : (b - c) ^ 3 ≠ 0 := pow_ne_zero 3 hbc
  have hquot : b * tateC10_K b c / (b - c) ^ 3 = 0 := by
    simpa using hrel.symm
  have hmul := congrArg (fun z : ℚ => z * (b - c) ^ 3) hquot
  field_simp [hbc3] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left hb
```

The remaining coordinate statement should be:

```lean
theorem tateC10_5P_eq
    {b c : ℚ} (hb : b ≠ 0) (hbc : b - c ≠ 0) :
    ∃ h5 : ((tateW b c)⁄ℚ).Nonsingular
        (tateC10_5P_x b c) (tateC10_5P_y b c),
      (5 : ℕ) • tateOriginAffine b c hb =
        WeierstrassCurve.Affine.Point.some
          (tateC10_5P_x b c) (tateC10_5P_y b c) h5
```

This is the best small coordinate residual if the full `P2+P3` proof is still noisy.

---

## 4. Tate parameter to short model

Once `K=0` and `tateC10_param_of_K` land:

```lean
let t := tateC10_tInv b c
have hden : tateC10_den t ≠ 0
have hbparam : b = tateC10_b t
have hcparam : c = tateC10_c t
```

The next residual should be only the coordinate conversion to the existing N10 short family.

```lean
structure TateC10Good (t : ℚ) : Prop where
  hden : tateC10_den t ≠ 0
  hDelta10 : Delta10 t ≠ 0

/-- Narrow residual B: pure variable-change algebra from the Tate C10 row to the N10 short model. -/
axiom tateC10_param_to_shortW
    (t : ℚ) (hden : tateC10_den t ≠ 0) :
    Delta10 t ≠ 0 ∧
      ∃ C : WeierstrassCurve.VariableChange ℚ,
        C • tateW (tateC10_b t) (tateC10_c t) = shortW (A10 t) (B10 t)
```

If `Delta10 t ≠ 0` depends on the transported nonsingularity rather than just `hden`, use this slightly more honest version:

```lean
axiom tateC10_param_to_shortW_of_tate_delta
    (t : ℚ) (hden : tateC10_den t ≠ 0)
    (hDeltaTate : (tateW (tateC10_b t) (tateC10_c t)).Δ ≠ 0) :
    Delta10 t ≠ 0 ∧
      ∃ C : WeierstrassCurve.VariableChange ℚ,
        C • tateW (tateC10_b t) (tateC10_c t) = shortW (A10 t) (B10 t)
```

I recommend the second statement because it avoids accidentally asserting that every `hden` parameter is nonsingular if the table row has other excluded values.

The algebra inside this residual should be `field_simp [hden]; ring` after unfolding the explicit variable change, `A10`, `B10`, `shortW`, `tateW`, `tateC10_b`, and `tateC10_c`.

---

## 5. Full two-torsion transport and short square lemma

These should be checked/generic, and likely already exist in N12 around the full two-torsion/short-model square section.

### Transport through variable changes

Use additive equivalences, not raw curve equality.

```lean
theorem FullTwoTorsionData.map_addEquiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (D : FullTwoTorsionData G) :
    FullTwoTorsionData H := by
  refine
    { T₁ := e D.T₁
      T₂ := e D.T₂
      T₃ := e D.T₃
      hT₁_two := by simpa using congrArg e D.hT₁_two
      hT₂_two := by simpa using congrArg e D.hT₂_two
      hT₃_two := by simpa using congrArg e D.hT₃_two
      hT₁_ne_zero := by intro h; exact D.hT₁_ne_zero (by simpa using congrArg e.symm h)
      hT₂_ne_zero := by intro h; exact D.hT₂_ne_zero (by simpa using congrArg e.symm h)
      hT₃_ne_zero := by intro h; exact D.hT₃_ne_zero (by simpa using congrArg e.symm h)
      hT₁_ne_T₂ := by intro h; exact D.hT₁_ne_T₂ (by simpa using congrArg e.symm h)
      hT₁_ne_T₃ := by intro h; exact D.hT₁_ne_T₃ (by simpa using congrArg e.symm h)
      hT₂_ne_T₃ := by intro h; exact D.hT₂_ne_T₃ (by simpa using congrArg e.symm h) }
```

For curve equality after `hCurve : C • E = W`, use `Eq.ndrec`/`subst hCurve` or the existing N12 transport wrapper.

### Short model square discriminant

This is the generic terminal lemma:

```lean
theorem short_quad_disc_square_of_quadratic_root
    {A B r : ℚ} (hr : r ^ 2 + A * r + B = 0) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  refine ⟨A + 2 * r, ?_⟩
  nlinarith [hr]

theorem shortW_square_of_full_two_torsion
    {A B : ℚ}
    (hfull : FullTwoTorsionData ((shortW A B)⁄ℚ).Point)
    (hOriginTwo : (0 : ℚ) is the distinguished x-root / or exact cyclic 10 image) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  -- Pick a nonzero 2-torsion point different from the distinguished `(0,0)`.
  -- It has affine coordinates `(r,0)` with `r≠0`, hence `r^2 + A*r + B=0`.
  -- Then apply `short_quad_disc_square_of_quadratic_root`.
  exact shortW_square_of_full_two_torsion_N12_reused hfull hOriginTwo
```

Do not assume the extra two-torsion point is arbitrary.  You need it **distinct from the distinguished two-torsion point** coming from `5P`; otherwise it may just be `(0,0)` and give no quadratic root.

---

## 6. Wrapper theorem replacing `kubert_C10_square`

Here is the final wrapper shape once residual A and residual B are in place.

```lean
theorem kubert_C10_square_reduced
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta10 t ≠ 0 ∧ s ^ 2 = A10 t ^ 2 - 4 * B10 t := by
  rcases hE with ⟨f, hf⟩
  let Gdata := C10GroupData.of_injective_zmod2_prod_zmod10 f hf

  rcases tate_normal_form_at_point_of_addOrder10 E Gdata.P Gdata.hP_order with
    ⟨b, c, hb, hDeltaTate, C0, hCurve0, hOrd10⟩

  have hc : c ≠ 0 :=
    tateC10_c_ne_zero_of_origin_order10 (b := b) (c := c) hb hOrd10
  have hbc : b - c ≠ 0 :=
    tateC10_b_sub_c_ne_zero_of_origin_order10 (b := b) (c := c) hb hOrd10
  have hK : tateC10_K b c = 0 :=
    tateC10_K_eq_zero_of_origin_order10 (b := b) (c := c) hb hOrd10

  let t : ℚ := tateC10_tInv b c
  have hparam := tateC10_param_of_K (b := b) (c := c) hc hbc hK
  have hden : tateC10_den t ≠ 0 := by simpa [t] using hparam.1
  have hbparam : b = tateC10_b t := by simpa [t] using hparam.2.1
  have hcparam : c = tateC10_c t := by simpa [t] using hparam.2.2

  have hDeltaTateParam :
      (tateW (tateC10_b t) (tateC10_c t)).Δ ≠ 0 := by
    simpa [hbparam, hcparam] using hDeltaTate

  rcases tateC10_param_to_shortW_of_tate_delta t hden hDeltaTateParam with
    ⟨hDelta10, C1, hShort⟩

  have hfull_tate : FullTwoTorsionData ((tateW b c)⁄ℚ).Point := by
    -- Transport `Gdata.fullTwo` through `C0` and `hCurve0` using the N12 wrappers.
    exact fullTwo_transport_variableChange_curve_eq
      (D := Gdata.fullTwo) (C := C0) (hCurve := hCurve0)

  have hfull_short : FullTwoTorsionData ((shortW (A10 t) (B10 t))⁄ℚ).Point := by
    -- Rewrite Tate parameters and transport through `C1` and `hShort`.
    subst hbparam
    subst hcparam
    exact fullTwo_transport_variableChange_curve_eq
      (D := hfull_tate) (C := C1) (hCurve := hShort)

  have hdistinguished :
      DistinguishedTwoTorsionFromCyclic10 (shortW (A10 t) (B10 t)) := by
    -- The image of `5 • P` becomes the distinguished `(0,0)` on the short model.
    -- This is usually part of the Tate-to-short conversion residual if not already proved.
    exact distinguished_two_torsion_of_tateC10_short_conversion
      (t := t) hden hShort

  rcases shortW_square_of_full_two_torsion
      (A := A10 t) (B := B10 t) hfull_short hdistinguished with
    ⟨s, hs⟩
  exact ⟨t, s, hDelta10, hs⟩
```

If `subst hbparam`/`subst hcparam` is awkward because they are equations in the wrong direction, replace that block by `simpa [hbparam, hcparam]` around the transport theorem.

---

## 7. Warnings / false routes

- **Do not skip `c≠0`.**  `tateC10_param_of_K` uses `t = c²/(b-c)`.  Exact order 10 must prove `c≠0`; otherwise the inverse parameter degenerates.
- **Do not use the explicit `5P` coordinates before proving `b-c≠0`.**  They have denominator `(b-c)`; `b=c` is the order-5 degeneration.
- **Do not claim full two-torsion survives a variable change by rewriting points directly.**  Use the additive equivalence for variable changes, then rewrite the target curve equality.
- **Do not assume the extra two-torsion point is the distinguished root.**  In the short model, the cyclic-10 point supplies one 2-torsion point, normally `(0,0)`.  Full two-torsion must provide a different one to get a nonzero root of `x² + A x + B`.
- **Do not assert `Delta10 t≠0` from `hden` alone unless you have checked the discriminant algebra.**  The safer residual takes the Tate discriminant nonzero as input:
  `tateC10_param_to_shortW_of_tate_delta`.
- **Normal-form construction is not essentially order 12.**  The only order-specific parts are the nonzero lemmas (`a₃≠0`, post-kill `a₂≠0`) and the final transported `addOrderOf = n`.

The immediate next axiom reduction I recommend is therefore:

```lean
axiom tate_normal_form_at_point_of_addOrder10
axiom tateC10_param_to_shortW_of_tate_delta
```

plus checked wrappers above.  That removes arbitrary full `ZMod 2 × ZMod 10` reasoning, C10 table algebra, and short-model square discrimination from the residual.
