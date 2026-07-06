ANSWER Q3567 baadebf5

# Q3567: `tendsto_sigma_atTop`

## Direct Mathlib API

Use the existing improper-integral tail theorem:

```lean
#check MeasureTheory.tendsto_integral_Ioi_zero
```

It has the shape

```lean
MeasureTheory.tendsto_integral_Ioi_zero
  (hb : Tendsto b l atTop) :
  Tendsto (fun i => ∫ x in Ioi (b i), f x ∂μ) l (𝓝 0)
```

It does **not** require you to pass integrability; internally it either finds some tail on which `f` is integrable, or all tail integrals are definitionally zero. In this use case we already have integrability from `rightIntegrand_integrableOn_Ioi_root`, but the direct theorem is still the shortest proof.

## Preferred code

```lean
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import FLT.Assumptions.MazurProof.RealTopologyS4

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace MazurProof.RealTopology

theorem tendsto_sigma_atTop
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto (sigma A B) atTop (𝓝 0) := by
  simpa [sigma] using
    (MeasureTheory.tendsto_integral_Ioi_zero
      (μ := volume)
      (f := rightIntegrand A B)
      (b := fun x : ℝ => x)
      (l := atTop)
      (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop))

end MazurProof.RealTopology
```

If Lean has trouble inferring the codomain, add the explicit type parameter:

```lean
    (MeasureTheory.tendsto_integral_Ioi_zero
      (E := ℝ)
      (μ := volume)
      (f := rightIntegrand A B)
      (b := fun x : ℝ => x)
      (l := atTop)
      (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop))
```

The hypotheses `hroot`, `hderiv`, and `hposRight` are unused in this proof. That is mathematically fine because the tail-limit theorem is stronger; it proves the limit for any function whose tail integrals are interpreted by Mathlib’s Bochner integral convention. If you want to make the proof visibly use the established analytic theorem, use the fallback below.

## Fallback proof using your integrability lemma

This is essentially the proof of `MeasureTheory.tendsto_integral_Ioi_zero` specialized to `a = e` and `b = id`.

```lean
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import FLT.Assumptions.MazurProof.RealTopologyS4

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace MazurProof.RealTopology

theorem tendsto_sigma_atTop'
    {A B e : ℝ}
    (hroot : shortCubic A B e = 0)
    (hderiv : 0 < shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < shortCubic A B u) :
    Tendsto (sigma A B) atTop (𝓝 0) := by
  classical
  let f : ℝ → ℝ := rightIntegrand A B
  have hfIoi : IntegrableOn f (Ioi e) volume := by
    simpa [f] using
      rightIntegrand_integrableOn_Ioi_root
        (A := A) (B := B) (e := e) hroot hderiv hposRight

  have hfinite_to_tail :
      Tendsto (fun x : ℝ => ∫ t in e..x, f t) atTop
        (𝓝 (∫ t in Ioi e, f t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := volume)
      (f := f)
      (a := e)
      hfIoi
      (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)

  have htail_eq :
      (fun x : ℝ => ∫ t in Ioi x, f t) =ᶠ[atTop]
        fun x : ℝ => (∫ t in Ioi e, f t) - ∫ t in e..x, f t := by
    filter_upwards [eventually_ge_atTop e] with x hx
    -- Mathlib theorem: `integral over (e,x] + integral over (x,∞) = integral over (e,∞)`.
    have hdecomp := intervalIntegral.integral_interval_add_Ioi
      (μ := volume)
      (f := f)
      hfIoi
      (hfIoi.mono_set (Ioi_subset_Ioi hx))
    -- `hdecomp` has RHS/LHS orientation depending on simp-normalization; this usually closes.
    rw [← sub_eq_iff_eq_add']
    simpa [intervalIntegral.integral_of_le hx] using hdecomp.symm

  have hsub :
      Tendsto (fun x : ℝ => (∫ t in Ioi e, f t) - ∫ t in e..x, f t)
        atTop (𝓝 0) := by
    simpa using (Tendsto.const_sub (∫ t in Ioi e, f t) hfinite_to_tail)

  have htail : Tendsto (fun x : ℝ => ∫ t in Ioi x, f t) atTop (𝓝 0) :=
    hsub.congr' htail_eq.symm

  simpa [sigma, f] using htail

end MazurProof.RealTopology
```

If the orientation of `integral_interval_add_Ioi` differs in your local build, replace the decomposition block with the exact pattern used in Mathlib:

```lean
  have htail_eq :
      (fun x : ℝ => (∫ t in Ioi e, f t) - ∫ t in e..x, f t) =ᶠ[atTop]
        fun x : ℝ => ∫ t in Ioi x, f t := by
    filter_upwards [eventually_ge_atTop e] with x hx
    rw [sub_eq_iff_eq_add',
      intervalIntegral.integral_interval_add_Ioi
        hfIoi (hfIoi.mono_set (Ioi_subset_Ioi hx))]
```

Then use

```lean
  exact Tendsto.congr' htail_eq hsub
```

## APIs involved

```lean
#check MeasureTheory.tendsto_integral_Ioi_zero
#check MeasureTheory.intervalIntegral_tendsto_integral_Ioi
#check intervalIntegral.integral_interval_add_Ioi
#check IntegrableOn.mono_set
#check Ioi_subset_Ioi
#check Tendsto.const_sub
#check Tendsto.congr'
#check eventually_ge_atTop
```

The one-line proof with `MeasureTheory.tendsto_integral_Ioi_zero` is the route I would commit first.