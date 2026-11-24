/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Missing integration by parts lemmas

-/

@[expose] public noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜]

open scoped InnerProductSpace SchwartzMap

section innerReal

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable (𝕜 E) in
/-- The inner product as a `ℝ`-bilinear map. -/
def innerRealₗ : E →ₗ[ℝ] E →ₗ[ℝ] 𝕜 :=
  LinearMap.mk₂ ℝ (inner 𝕜) ?_ ?_ ?_ ?_
where finally
  · simp [inner_add_left]
  · intro c x y
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) c x, inner_smul_left]
    simp [RCLike.real_smul_eq_coe_mul]
  · simp [inner_add_right]
  · intro c x y
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) c y, inner_smul_right]
    simp [RCLike.real_smul_eq_coe_mul]

@[simp]
theorem innerRealₗ_apply (x y : E) : innerRealₗ 𝕜 E x y = inner 𝕜 x y := rfl

@[simp]
theorem innerRealₗ_eq_innerₗ : innerRealₗ ℝ F = innerₗ F := rfl

variable (𝕜 E) in
/-- The inner product as a continuous `ℝ`-bilinear map. -/
def innerRealL : E →L[ℝ] E →L[ℝ] 𝕜 :=
  LinearMap.mkContinuous₂ (innerRealₗ 𝕜 E) 1 (by simpa using norm_inner_le_norm)

@[simp]
theorem innerRealL_apply (x y : E) : innerRealL 𝕜 E x y = inner 𝕜 x y := rfl

@[simp]
theorem innerRealL_eq_innerSL : innerRealL ℝ F = innerSL ℝ := rfl

end innerReal


variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open MeasureTheory

open scoped LineDeriv Laplacian

variable {μ : Measure E} [μ.IsAddHaarMeasure]


namespace SchwartzMap

/-- Integration by parts of Schwartz functions for directional derivatives.

Version for the inner product. -/
theorem integral_inner_lineDerivOp_right_eq_neg_left (f : 𝓢(E, F)) (g : 𝓢(E, F)) (v : E) :
    ∫ (x : E), ⟪f x, ∂_{v} g x⟫_𝕜 ∂μ = -∫ (x : E), ⟪∂_{v} f x, g x⟫_𝕜 ∂μ := by
  apply integral_bilinear_lineDerivOp_right_eq_neg_left f g (innerRealL 𝕜 F) v

/-- Integration by parts of Schwartz functions for the Laplacian.

Version for the inner product. -/
theorem integral_inner_laplacian_right_eq_left (f : 𝓢(E, F)) (g : 𝓢(E, F)) :
    ∫ (x : E), ⟪f x, Δ g x⟫_𝕜 ∂μ = ∫ (x : E), ⟪Δ f x, g x⟫_𝕜 ∂μ := by
  apply integral_bilinear_laplacian_right_eq_left f g (innerRealL 𝕜 F)

end SchwartzMap
