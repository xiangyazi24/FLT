# Q2994 (dm-codex1): shrinking/replacing `kubert_C10_square`

I could not inspect the current local `KubertBridgeN10.lean` through the GitHub connector: the accessible GitHub contents API returned `404` for the path, so this plan is based on the self-contained declarations in the prompt and on the N12 route you described.

The right N10 replacement is strictly parallel to the now-eliminated N12 bridge, but the arithmetic is easier.  The residual should be split into:

1. group extraction from `ZMod 2 × ZMod 10`;
2. order-10 Tate normalization;
3. the C10 Tate table row;
4. conversion to the checked `shortW (A10 t) (B10 t)` family;
5. a general short-model lemma: full rational 2-torsion gives a square quadratic discriminant.

The best intermediate shrink is to replace `kubert_C10_square` by only the Tate/short conversion residual, leaving group extraction and full-2 square as checked general lemmas.

## 1. C10 Tate row

Use the same Tate normal form as N12:

```lean
-- y^2 + (1-c)xy - b y = x^3 - b x^2
-- P=(0,0)
```

For C10, the one-parameter table row can be written as follows.

```lean
def tateC10_den (t : ℚ) : ℚ :=
  t ^ 2 - 3 * t + 1

def tateC10_b (t : ℚ) : ℚ :=
  t ^ 3 * (t - 1) * (2 * t - 1) / (tateC10_den t) ^ 2

def tateC10_c (t : ℚ) : ℚ :=
  - t * (t - 1) * (2 * t - 1) / tateC10_den t
```

The inverse parameter on the nondegenerate table component is

```lean
def tateC10_tInv (b c : ℚ) : ℚ :=
  c ^ 2 / (b - c)
```

The table condition is most Lean-friendly if encoded as the `5P` two-torsion numerator.  Let `d=b-c`.  The computation of `5P = 2P+3P` gives

```lean
def tateC10_K (b c : ℚ) : ℚ :=
  let d : ℚ := b - c
  - d ^ 3 + (3 * c ^ 2 - c) * d ^ 2 + (3 * c ^ 3 - c ^ 4) * d - 2 * c ^ 5
```

The exact table lemmas to add are:

```lean
theorem tateC10_K_of_param
    (t : ℚ) (hden : tateC10_den t ≠ 0) :
    tateC10_K (tateC10_b t) (tateC10_c t) = 0 := by
  dsimp [tateC10_K, tateC10_b, tateC10_c, tateC10_den]
  field_simp [hden]
  ring

theorem tateC10_param_of_K
    {b c : ℚ}
    (hc : c ≠ 0) (hbc : b - c ≠ 0)
    (hK : tateC10_K b c = 0) :
    let t := tateC10_tInv b c
    tateC10_den t ≠ 0 ∧
      b = tateC10_b t ∧ c = tateC10_c t := by
  intro t
  -- Recommended proof route:
  --   set u = (b-c)/c;
  --   K=0 becomes
  --     (u+2)c^2 - 3*u*(u+1)*c + u^2*(u+1) = 0;
  --   with t=c/u=c^2/(b-c), solve by field_simp/ring.
  -- The closed forms are:
  --   u = - (t-1)*(2*t-1)/(t^2-3*t+1)
  --   c = - t*(t-1)*(2*t-1)/(t^2-3*t+1)
  --   b = t^3*(t-1)*(2*t-1)/(t^2-3*t+1)^2
  have hu_ne : (b - c) / c ≠ 0 := by
    exact div_ne_zero hbc hc
  have ht_eq : t = c ^ 2 / (b - c) := rfl
  -- If `field_simp` leaves inverse powers, introduce the two local facts below:
  have hbc' : b - c ≠ 0 := hbc
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  -- The rest should be a local algebra block.  I recommend proving these as three
  -- private lemmas first:
  --   tateC10_den_tInv_ne_zero_of_K
  --   tateC10_b_tInv_eq_of_K
  --   tateC10_c_tInv_eq_of_K
  -- each with `field_simp [hc, hbc, hK]` followed by `ring_nf at hK ⊢; nlinarith`.
  exact tateC10_param_of_K_algebra hc hbc hK
```

I would actually implement the inverse theorem through three private algebra lemmas instead of one large `field_simp` proof:

```lean
private theorem tateC10_K_as_conic
    {b c : ℚ} (hc : c ≠ 0) :
    let u : ℚ := (b - c) / c
    tateC10_K b c =
      c ^ 3 *
        (-(u ^ 3) + (3*c - 1) * u ^ 2 + (3*c - c ^ 2) * u - 2*c ^ 2) := by
  intro u
  dsimp [tateC10_K]
  field_simp [hc]
  ring

private theorem tateC10_conic_param_forward
    (t : ℚ) (hden : tateC10_den t ≠ 0) :
    let u : ℚ := - (t - 1) * (2*t - 1) / tateC10_den t
    let c : ℚ := - t * (t - 1) * (2*t - 1) / tateC10_den t
    -(u ^ 3) + (3*c - 1) * u ^ 2 + (3*c - c ^ 2) * u - 2*c ^ 2 = 0 := by
  intro u c
  dsimp [tateC10_den]
  field_simp [hden]
  ring

private theorem tateC10_conic_param_inverse
    {u c : ℚ} (hu : u ≠ 0)
    (hconic : -(u ^ 3) + (3*c - 1) * u ^ 2 + (3*c - c ^ 2) * u - 2*c ^ 2 = 0) :
    let t : ℚ := c / u
    tateC10_den t ≠ 0 ∧
      u = - (t - 1) * (2*t - 1) / tateC10_den t ∧
      c = - t * (t - 1) * (2*t - 1) / tateC10_den t := by
  intro t
  -- This is the same line-through-(0,0) parametrization:
  --   c = t*u
  -- substituted into
  --   (u+2)c^2 - 3u(u+1)c + u^2(u+1)=0.
  -- The denominator is `t^2 - 3t + 1`.
  exact tateC10_conic_param_inverse_algebra hu hconic
```

The last two `*_algebra` placeholders are not mathematical residuals; they should be private `field_simp; ring_nf; nlinarith` lemmas.  If you want the smallest possible git step, add them as temporary local axioms/residuals, not the global `kubert_C10_square`.

## 2. Direct `5P` computation giving the table condition

The key affine computation is:

```lean
def tateC10_5P_D (b c : ℚ) : ℚ := b - c

def tateC10_5P_L (b c : ℚ) : ℚ :=
  (b - c - b*c) / (c - b)

def tateC10_5P_nu (b c : ℚ) : ℚ :=
  b * (c ^ 2 + c - b) / (c - b)

def tateC10_5P_x (b c : ℚ) : ℚ :=
  - b * c * (b - c - c ^ 2) / (b - c) ^ 2

def tateC10_5P_y (b c : ℚ) : ℚ :=
  - (tateC10_5P_L b c + (1 - c)) * tateC10_5P_x b c -
    tateC10_5P_nu b c + b
```

Then:

```lean
theorem tateC10_psi2_5P_eq_K_div
    {b c : ℚ} (hb : b ≠ 0) (hbc : b - c ≠ 0) :
    tatePsi2 b c (tateC10_5P_x b c) (tateC10_5P_y b c) =
      b * tateC10_K b c / (b - c) ^ 3 := by
  have hbc2 : (b - c) ^ 2 ≠ 0 := pow_ne_zero 2 hbc
  have hbc3 : (b - c) ^ 3 ≠ 0 := pow_ne_zero 3 hbc
  dsimp [tatePsi2, tateC10_5P_x, tateC10_5P_y, tateC10_5P_L,
    tateC10_5P_nu, tateC10_K]
  field_simp [hbc, hbc2, hbc3]
  ring
```

Order 10 gives `5P` two-torsion, hence the left side is zero.  The only denominator is `b-c`; if `b=c`, then the original Tate point has order 5, not 10, so exact order 10 supplies `b-c≠0`.

Recommended wrappers:

```lean
theorem tateC10_b_sub_c_ne_zero_of_origin_order10
    {b c : ℚ} (hb : b ≠ 0)
    (hOrd : addOrderOf (tateOriginAffine b c hb) = 10) :
    b - c ≠ 0 := by
  intro hbc
  have hbc_eq : b = c := sub_eq_zero.mp hbc
  -- Existing N12-style Tate table/multiple facts should prove order 5 when b=c.
  have h5 : addOrderOf (tateOriginAffine b c hb) = 5 := by
    exact tate_origin_order_eq_five_of_b_eq_c hb hbc_eq
  omega

theorem tateC10_K_eq_zero_of_origin_order10
    {b c : ℚ} (hb : b ≠ 0)
    (hOrd : addOrderOf (tateOriginAffine b c hb) = 10) :
    tateC10_K b c = 0 := by
  have hbc : b - c ≠ 0 :=
    tateC10_b_sub_c_ne_zero_of_origin_order10 (b := b) (c := c) hb hOrd
  have hpsi : tatePsi2 b c (tateC10_5P_x b c) (tateC10_5P_y b c) = 0 := by
    -- group-law route:
    --   prove `5 • tateOriginAffine b c hb` has coordinates
    --     `(tateC10_5P_x b c, tateC10_5P_y b c)`;
    --   exact order 10 gives `2 • (5P)=0`;
    --   for Tate form, affine 2-torsion is `tatePsi2=0`.
    exact tatePsi2_5P_eq_zero_of_origin_order10 hb hOrd
  have hrel := tateC10_psi2_5P_eq_K_div (b := b) (c := c) hb hbc
  rw [hpsi] at hrel
  have hbc3 : (b - c) ^ 3 ≠ 0 := pow_ne_zero 3 hbc
  have hbden : b / (b - c) ^ 3 ≠ 0 := div_ne_zero hb hbc3
  -- From `0 = b*K/(b-c)^3`, clear denominators.
  field_simp [hb, hbc, hbc3] at hrel
  exact hrel
```

This is the C10 analog of the N12 `ψ₄`-core step.  It is small and computational.

## 3. Short model and the square discriminant

For the current file, keep using the existing `A10`, `B10`, `Delta10`, and checked:

```lean
quad_disc_identity : A10 t ^ 2 - 4 * B10 t = 256 * t ^ 5 * (t ^ 2 + t - 1)
```

The universal C10 short-model theorem should be stated as:

```lean
theorem tateC10_param_to_shortW
    (t : ℚ) (hgood : TateC10Good t) :
    ∃ C : WeierstrassCurve.VariableChange ℚ,
      C • tateW (tateC10_b t) (tateC10_c t) = shortW (A10 t) (B10 t) := by
  -- This is pure coordinate conversion from the Tate row to the current N10 short family.
  -- Expected proof: unfold `shortW`, `A10`, `B10`, `tateW`, `tateC10_b`, `tateC10_c`,
  -- the explicit variable change, then `field_simp [hgood.den_ne] ; ring`.
  exact tateC10_param_to_shortW_algebra t hgood
```

If `A10/B10` use a different parameter than the `t` above, do **not** change the group-law proof.  Add a parameter-change theorem:

```lean
def tateC10_to_A10_param (t : ℚ) : ℚ :=
  -- fill with the local file's parameter, if different
  t

theorem tateC10_param_to_shortW_reparam
    (t : ℚ) (hgood : TateC10Good t) :
    ∃ C : WeierstrassCurve.VariableChange ℚ,
      C • tateW (tateC10_b t) (tateC10_c t) =
        shortW (A10 (tateC10_to_A10_param t))
               (B10 (tateC10_to_A10_param t)) := by
  -- field_simp/ring
  exact tateC10_param_to_shortW_algebra_reparam t hgood
```

### General square lemma for short models

This is the key replacement for the “full 2-torsion forces square discriminant” part of the axiom.

```lean
theorem short_quad_disc_square_of_quadratic_root
    {A B r : ℚ} (hr : r ^ 2 + A * r + B = 0) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  refine ⟨A + 2 * r, ?_⟩
  nlinarith [hr]
```

For the actual curve:

```lean
theorem shortW_square_of_extra_two_torsion
    {A B : ℚ}
    (h_extra_root : ∃ r : ℚ, r ≠ 0 ∧ r ^ 2 + A * r + B = 0) :
    ∃ s : ℚ, s ^ 2 = A ^ 2 - 4 * B := by
  rcases h_extra_root with ⟨r, _hr0, hr⟩
  exact short_quad_disc_square_of_quadratic_root hr
```

The group-theoretic bridge from `ZMod 2 × ZMod 10` should produce `h_extra_root` after transporting the two independent 2-torsion points to `shortW (A10 t) (B10 t)`.  In a short model

```text
y^2 = x^3 + A*x^2 + B*x = x*(x^2 + A*x + B),
```

2-torsion has `y=0`.  The known cyclic-10 point supplies the root `x=0` (`5P`).  Any independent 2-torsion point must have `x≠0`, hence gives a root of `x^2 + A*x + B`.

Lean skeleton:

```lean
theorem extra_quadratic_root_of_full_two_shortW
    {A B : ℚ}
    (hfull : FullRationalTwoTorsion (shortW A B)) :
    ∃ r : ℚ, r ≠ 0 ∧ r ^ 2 + A * r + B = 0 := by
  -- Extract a nonzero 2-torsion point not equal to `(0,0)`.
  rcases hfull.exists_two_torsion_ne_origin with ⟨R, hR2, hRne0, hRneOrigin⟩
  rcases R with _ | ⟨x, y, hxy⟩
  · contradiction
  have hy : y = 0 := by
    -- on shortW, `2R=0` gives `R=-R`; negation is `(x,-y)`;
    -- char zero gives `2*y=0`, hence y=0.
    exact shortW_y_eq_zero_of_two_torsion (A := A) (B := B) hxy hR2
  have hcurve : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x := by
    exact shortW_affine_equation hxy
  have hxpoly : x * (x ^ 2 + A * x + B) = 0 := by
    nlinarith [hcurve, hy]
  have hx0 : x ≠ 0 := by
    intro hx
    apply hRneOrigin
    -- point equality to `(0,0)` by `hx` and `hy` plus proof irrelevance.
    ext <;> simp [hx, hy]
  have hquad : x ^ 2 + A * x + B = 0 := by
    exact (mul_eq_zero.mp hxpoly).resolve_left hx0
  exact ⟨x, hx0, hquad⟩
```

This lemma is independent of N10 and should live in a common short-Weierstrass helper section.

## 4. Group extraction from `ZMod 2 × ZMod 10`

Add small group lemmas rather than coding them inline.

```lean
theorem exact_order10_point_of_ZMod2_prod_ZMod10_injection
    {G : Type*} [AddCommGroup G]
    (f : (ZMod 2 × ZMod 10) →+ G) (hf : Function.Injective f) :
    ∃ P : G, addOrderOf P = 10 := by
  refine ⟨f (0, 1), ?_⟩
  -- `addOrderOf (0,1) = 10`; injective hom preserves exact order.
  simpa using addOrderOf_map_of_injective f hf (0, 1)

theorem full_two_of_ZMod2_prod_ZMod10_injection
    {G : Type*} [AddCommGroup G]
    (f : (ZMod 2 × ZMod 10) →+ G) (hf : Function.Injective f) :
    FullTwoSubgroup G := by
  -- The three nonzero 2-torsion elements are `(1,0)`, `(0,5)`, `(1,5)`.
  -- Their images are distinct by `hf` and have order 2.
  exact fullTwoSubgroup_of_three_distinct_order_two
    (f (1,0)) (f (0,5)) (f (1,5))
    (by simpa using addOrderOf_map_of_injective f hf (1,0))
    (by simpa using addOrderOf_map_of_injective f hf (0,5))
    (by simpa using addOrderOf_map_of_injective f hf (1,5))
    (by intro h; exact by simpa using hf h)
    (by intro h; exact by simpa using hf h)
    (by intro h; exact by simpa using hf h)
```

Use the local names already present for the project’s “full two torsion” structure, if any.  If there is no such structure, use a theorem that directly returns a transported extra quadratic root after normalization.

## 5. Proposed final theorem chain

The replacement for `kubert_C10_square` should become:

```lean
theorem kubert_C10_square_no_axiom
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta10 t ≠ 0 ∧ s ^ 2 = A10 t ^ 2 - 4 * B10 t := by
  rcases hE with ⟨f, hf⟩
  rcases exact_order10_point_of_ZMod2_prod_ZMod10_injection f hf with ⟨P, hP10⟩

  -- N12-normalization machinery generalized to exact order 10.
  rcases tate_normal_form_at_point_of_addOrder10 E P hP10 with
    ⟨b, c, hb, hDelta, C0, hCurve0, hOriginOrder10⟩

  have hK : tateC10_K b c = 0 :=
    tateC10_K_eq_zero_of_origin_order10 (b := b) (c := c) hb hOriginOrder10

  have hc : c ≠ 0 := tate_c_ne_zero_of_origin_order10 (b := b) (c := c) hb hOriginOrder10
  have hbc : b - c ≠ 0 :=
    tateC10_b_sub_c_ne_zero_of_origin_order10 (b := b) (c := c) hb hOriginOrder10

  let t : ℚ := tateC10_tInv b c
  rcases tateC10_param_of_K (b := b) (c := c) hc hbc hK with
    ⟨hden, hbparam, hcparam⟩

  have hgood : TateC10Good t := by
    exact TateC10Good.of_param_data hden hbparam hcparam hDelta

  rcases tateC10_param_to_shortW t hgood with ⟨C1, hShort⟩

  have hfull_short : FullRationalTwoTorsion (shortW (A10 t) (B10 t)) := by
    -- Transport full 2-torsion through C0 and C1 additive equivalences.
    exact full_two_transport_variableChange_two_steps
      (f := f) (hf := hf) (C0 := C0) (C1 := C1)
      (hCurve0 := hCurve0) (hShort := hShort)

  rcases extra_quadratic_root_of_full_two_shortW hfull_short with ⟨r, hr0, hr⟩
  rcases short_quad_disc_square_of_quadratic_root (A := A10 t) (B := B10 t) hr with
    ⟨s, hs⟩

  have hDelta10 : Delta10 t ≠ 0 := by
    -- Either from hgood, or from non-singularity transported to shortW.
    exact Delta10_ne_zero_of_TateC10Good hgood

  exact ⟨t, s, hDelta10, hs⟩
```

## 6. Reuse N12 helpers or copy?

Do **not** import `KubertBridgeN12.lean` into `KubertBridgeN10.lean` unless you verify there is no import cycle.  The better layout is:

```text
KubertTateNormalForm.lean
  order-agnostic variable-change/affine-point machinery:
    affine extraction
    translate to origin
    killA4
    scale to Tate
    additive equivalence/order transport
    shortW full-two square lemmas

KubertBridgeN12.lean imports KubertTateNormalForm
KubertBridgeN10.lean imports KubertTateNormalForm
```

If you want the smallest patch, copy the N12 helper block into N10 under N10 names.  But the cleaner long-term move is a common helper file because N10 needs exactly the same variable-change infrastructure; only the exact order-specific obstruction lemmas change from `12` to `10`.

The order-specific missing lemmas for N10 are:

```lean
theorem origin_a3_ne_zero_of_addOrderOf_eq_10
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hO : (W⁄ℚ).Nonsingular 0 0)
    (hOrd : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 10) :
    W.a₃ ≠ 0

theorem origin_a2_ne_zero_of_addOrderOf_eq_10_of_a4_a6
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hO : (W⁄ℚ).Nonsingular 0 0)
    (hOrd : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 10)
    (hA4 : W.a₄ = 0) (hA6 : W.a₆ = 0) :
    W.a₂ ≠ 0

theorem tate_normal_form_at_point_of_addOrder10
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 10) :
    TateNormalFormAtOrder10 E
```

These should be cloned from the N12 proofs with the final divisibility contradictions changed from `12 ∣ n` to `10 ∣ n`.  The same group-law degeneracy facts apply: `a₃=0` makes the origin 2-torsion; the post-`killA4` `a₂=0` degeneracy gives order dividing 3 or 5 depending on the local formula, in either case contradicting exact order 10.

## 7. Smallest honest residual if full elimination is too large

The smallest replacement residual, strictly smaller than the current axiom, is:

```lean
/-- Pure Tate/table residual only: no arbitrary curve, no full group injection. -/
axiom tateC10_order10_to_short_param
    {b c : ℚ} (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0)
    (hOrd : addOrderOf (tateOriginAffine b c hb) = 10) :
    ∃ t : ℚ,
      Delta10 t ≠ 0 ∧
      ∃ C : WeierstrassCurve.VariableChange ℚ,
        C • tateW b c = shortW (A10 t) (B10 t)
```

Then prove the rest now:

```lean
theorem kubert_C10_square_of_tate_residual
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta10 t ≠ 0 ∧ s ^ 2 = A10 t ^ 2 - 4 * B10 t := by
  -- checked group extraction + checked order-10 Tate normal form + residual above
  -- + checked full-two transport + checked shortW square lemma.
  exact kubert_C10_square_from_tateC10_order10_to_short_param hE
```

This residual is much smaller than `kubert_C10_square`: it is only the cyclic-10 Tate table/short-model conversion.  It no longer talks about arbitrary curves or the full `ZMod 2 × ZMod 10` embedding.

The next smaller residual after that is purely algebraic:

```lean
axiom tateC10_param_to_shortW_algebra
    (t : ℚ) (hgood : TateC10Good t) :
    ∃ C : WeierstrassCurve.VariableChange ℚ,
      C • tateW (tateC10_b t) (tateC10_c t) = shortW (A10 t) (B10 t)
```

Everything else above should be checkable using the N12 infrastructure and `ring`/`field_simp`.
