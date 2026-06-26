# Q705 (dm1): domain proof of `formalAddX` divisibility

```lean
import scratch.FormalGroupW

open MvPowerSeries Finsupp WeierstrassCurve

variable {R : Type*} [CommRing R]

private theorem formalAddX_dvd_cube_of_noZeroDivisors
    {S : Type*} [CommRing S] [NoZeroDivisors S] [Nontrivial S]
    (V : WeierstrassCurve S) :
    (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S) ^ 3 ∣ V.formalAddX := by
  classical
  let A : Type := MvPowerSeries (Fin 2) S
  let W' : WeierstrassCurve.Projective A := (V.map (MvPowerSeries.C (σ := Fin 2))).toProjective
  let P : Fin 3 → A := V.formalPointMv (0 : Fin 2)
  let Q : Fin 3 → A := V.formalPointMv (1 : Fin 2)
  let Δ : A := MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)
  let yΔ : A := P (1 : Fin 3) * Q (2 : Fin 3) - Q (1 : Fin 3) * P (2 : Fin 3)
  let xΔ : A := P (0 : Fin 3) * Q (2 : Fin 3) - Q (0 : Fin 3) * P (2 : Fin 3)
  let den : A := P (2 : Fin 3) * Q (2 : Fin 3)

  have hP : W'.Equation P := by
    simpa [W', P] using V.formalPointMv_equation (0 : Fin 2)
  have hQ : W'.Equation Q := by
    simpa [W', Q] using V.formalPointMv_equation (1 : Fin 2)

  -- `addX_eq'`, specialized to the two formal points.
  have h_addX := WeierstrassCurve.Projective.addX_eq'
      (W' := W') (P := P) (Q := Q) hP hQ
  change W'.addX P Q * den ^ 2 =
      (yΔ ^ 2 * den
        + W'.a₁ * yΔ * den * xΔ
        - W'.a₂ * den * xΔ ^ 2
        - P (0 : Fin 3) * Q (2 : Fin 3) * xΔ ^ 2
        - Q (0 : Fin 3) * P (2 : Fin 3) * xΔ ^ 2) * xΔ at h_addX

  -- The two basic divided-difference facts for the formal point coordinates.
  have hyΔ : Δ ∣ yΔ := by
    dsimp [yΔ, P, Q, Δ]
    simpa [WeierstrassCurve.formalPointMv_y, WeierstrassCurve.formalPointMv_z,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      V.formalW_X0_sub_formalW_X1_dvd

  have hxΔ : Δ ∣ xΔ := by
    dsimp [xΔ, P, Q, Δ]
    simpa [WeierstrassCurve.formalPointMv_x, WeierstrassCurve.formalPointMv_z,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      V.formalX_mul_formalW_X1_sub_X1_mul_formalW_X0_dvd

  -- The parenthesized `addX_eq'` bracket has two powers of `Δ`.
  have hbracket :
      Δ ^ 2 ∣
        yΔ ^ 2 * den
          + W'.a₁ * yΔ * den * xΔ
          - W'.a₂ * den * xΔ ^ 2
          - P (0 : Fin 3) * Q (2 : Fin 3) * xΔ ^ 2
          - Q (0 : Fin 3) * P (2 : Fin 3) * xΔ ^ 2 := by
    refine dvd_add ?_ (dvd_add ?_ (dvd_add ?_ ?_))
    · exact dvd_mul_of_dvd_left (mul_dvd_mul hyΔ hyΔ) den
    · exact dvd_mul_of_dvd_left (mul_dvd_mul hyΔ hxΔ) (W'.a₁ * den)
    · exact dvd_neg.mpr <| dvd_mul_of_dvd_right (mul_dvd_mul hxΔ hxΔ) (W'.a₂ * den)
    · refine dvd_add ?_ ?_
      · exact dvd_neg.mpr <|
          dvd_mul_of_dvd_right (mul_dvd_mul hxΔ hxΔ)
            (P (0 : Fin 3) * Q (2 : Fin 3))
      · exact dvd_neg.mpr <|
          dvd_mul_of_dvd_right (mul_dvd_mul hxΔ hxΔ)
            (Q (0 : Fin 3) * P (2 : Fin 3))

  -- Hence the right-hand side of `addX_eq'` has three powers of `Δ`.
  have h_rhs :
      Δ ^ 3 ∣
        (yΔ ^ 2 * den
          + W'.a₁ * yΔ * den * xΔ
          - W'.a₂ * den * xΔ ^ 2
          - P (0 : Fin 3) * Q (2 : Fin 3) * xΔ ^ 2
          - Q (0 : Fin 3) * P (2 : Fin 3) * xΔ ^ 2) * xΔ := by
    simpa [pow_succ, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      mul_dvd_mul hbracket hxΔ

  have h_mul_den : Δ ^ 3 ∣ W'.addX P Q * den ^ 2 := by
    rw [h_addX]
    exact h_rhs

  -- This is the cancellation lemma already used in the `formalAddZ` domain proof:
  -- `Pz = X₀³ u₀`, `Qz = X₁³ u₁`, `u₀` and `u₁` are units, and the regularity/coprimality
  -- facts for `X₀ - X₁` with `X₀` and `X₁` allow cancellation of `den ^ 2`.
  have h_cancel : Δ ^ 3 ∣ W'.addX P Q :=
    V.X_sub_X_cube_dvd_of_dvd_mul_formalPointMv_z_sq h_mul_den

  simpa [A, W', P, Q, Δ, den, WeierstrassCurve.formalAddX] using h_cancel
```
