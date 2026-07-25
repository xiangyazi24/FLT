import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The exact full rational hat-X identity, proved by Route A:
derive the selected branch and shifted curve equations, clear fractions on
`(x₁-r)^2` times the goal, use the scaled compact certificate, and cancel. -/
example
    (x₁ x₂ y₁ y₂ A B r : Rat)
    (hcurve₁ : y₁ ^ 2 = x₁ ^ 3 + A * x₁ + B)
    (hcurve₂ : y₂ ^ 2 = x₂ ^ 3 + A * x₂ + B)
    (htors : r ^ 3 + A * r + B = 0)
    (hat : (x₁ - r) * (x₂ - r) = 3 * r ^ 2 + A)
    (ha₁ : x₁ - r ≠ 0)
    (_ha₂ : x₂ - r ≠ 0)
    (hd : x₁ - x₂ ≠ 0)
    (h_ya_ne : y₁ * (x₂ - r) - y₂ * (x₁ - r) ≠ 0)
    (hy₁ : y₁ ≠ 0)
    (hx₃r_poly :
      (y₁ - y₂) ^ 2
          - x₁ * (x₁ - x₂) ^ 2
          - x₂ * (x₁ - x₂) ^ 2
          - (x₁ - x₂) ^ 2 * r ≠ 0) :
    let t : Rat := 3 * r ^ 2 + A
    let ell : Rat := (y₁ - y₂) / (x₁ - x₂)
    let x₃ : Rat := ell ^ 2 - x₁ - x₂
    let X₁ : Rat := x₁ + t / (x₁ - r)
    let Y₁ : Rat := y₁ * ((x₁ - r) ^ 2 - t) / (x₁ - r) ^ 2
    let ell' : Rat := (3 * X₁ ^ 2 + (A - 5 * t)) / (2 * Y₁)
    ell' ^ 2 - 2 * X₁ = x₃ + t / (x₃ - r) := by
  dsimp

  -- Step 1: choose the branch excluded by h_ya_ne.
  have hm :
      y₁ * (x₂ - r) + y₂ * (x₁ - r) = 0 := by
    have hprod :
        (y₁ * (x₂ - r) - y₂ * (x₁ - r)) *
            (y₁ * (x₂ - r) + y₂ * (x₁ - r)) = 0 := by
      linear_combination
          (x₂ - r) ^ 2 * hcurve₁
        - (x₁ - r) ^ 2 * hcurve₂
        + ((x₂ - r) ^ 2 - (x₁ - r) ^ 2) * htors
        + ((x₁ - r) * (x₂ - r) * (x₁ - x₂)) * hat
    exact (mul_eq_zero.mp hprod).resolve_left h_ya_ne

  -- Step 2: the shifted source-curve equation on the hat locus.
  have hE :
      y₁ ^ 2 - (x₁ - r) ^ 2 * (x₁ + x₂ + r) = 0 := by
    linear_combination hcurve₁ + htors - (x₁ - r) * hat

  -- Step 3: eliminate B exactly as requested.
  have hB : B = -(r ^ 3 + A * r) := by
    linear_combination htors

  -- Targeted hat rewrites.  These avoid rewriting bare A recursively through
  -- the very large rational expression.
  have ht :
      3 * r ^ 2 + A = (x₁ - r) * (x₂ - r) := hat.symm
  have hAp :
      A - 5 * (3 * r ^ 2 + A) =
        ((x₁ - r) * (x₂ - r) - 3 * r ^ 2)
          - 5 * ((x₁ - r) * (x₂ - r)) := by
    linear_combination 4 * hat

  have he :
      (x₁ - r) ^ 2 - (x₁ - r) * (x₂ - r) ≠ 0 := by
    rw [show
      (x₁ - r) ^ 2 - (x₁ - r) * (x₂ - r) =
        (x₁ - r) * (x₁ - x₂) by ring]
    exact mul_ne_zero ha₁ hd

  have hz :
      (y₁ - y₂) ^ 2
          - (x₁ - x₂) ^ 2 * (x₁ + x₂ + r) ≠ 0 := by
    intro hz0
    apply hx₃r_poly
    calc
      (y₁ - y₂) ^ 2
            - x₁ * (x₁ - x₂) ^ 2
            - x₂ * (x₁ - x₂) ^ 2
            - (x₁ - x₂) ^ 2 * r =
          (y₁ - y₂) ^ 2
            - (x₁ - x₂) ^ 2 * (x₁ + x₂ + r) := by ring
      _ = 0 := hz0

  -- `field_simp` ring-normalizes the x₃-r numerator before looking up its
  -- nonzero proof, so retain a hypothesis in exactly that normal form.
  have hz_nf := hz
  ring_nf at hz_nf

  -- Compact B-free coefficient names.
  let u : Rat := x₁ - r
  let v : Rat := x₂ - r
  let s : Rat := x₁ - x₂
  let U : Rat := u + v
  let T : Rat := x₁ + x₂ + r
  let d : Rat := y₁ - y₂
  let z : Rat := d ^ 2 - s ^ 2 * T
  let K : Rat := u * d + U * y₁
  let cE : Rat :=
    u ^ 2 * s ^ 6
      - 4 * z *
          (y₁ ^ 2 * U ^ 2
            + u ^ 2 * U * (s ^ 2 + U * T))
  let cM : Rat :=
    K * (4 * z * y₁ ^ 2 - u ^ 2 * s ^ 4)

  -- Step 7 is represented by this cancellation combinator.  Its remaining
  -- subgoal is exactly u^2 times the original rational equality.
  refine mul_left_cancel₀ (pow_ne_zero 2 ha₁) ?_

  -- Step 4.  Mentioning the hypotheses makes this robust even when the
  -- standalone simplified X-formula itself has no remaining B occurrence.
  simp only [hB] at hcurve₁ hcurve₂ htors ⊢

  -- Put the rational goal on the hat locus without reducing its denominator.
  rw [hAp, ht]

  -- Steps 5-6.  Literal field_simp cross-multiplies the two sides, so its
  -- polynomial is (x₁-x₂)^2 times the primitive u^2*N₀ certificate.
  field_simp [hy₁, ha₁, hd, he, hz, hz_nf]
  linear_combination
      ((x₁ - x₂) ^ 2 * cE) * hE
    + ((x₁ - x₂) ^ 2 * cM) * hm
