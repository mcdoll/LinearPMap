/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import all Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import Mathlib.Analysis.Fourier.LpSpace
public import LinearPMap.Analysis.Distribution.Sobolev

/-! # Sobolev spaces -/

@[expose] public noncomputable section

attribute [fun_prop] DenseRange Function.Surjective Function.Surjective.denseRange DenseRange.comp

variable {E F : Type*}

section Lp

open BoundedContinuousFunction MeasureTheory Lp

section BCF

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]

open scoped ENNReal
open BoundedContinuousFunction MeasureTheory

/-- Constructs a bounded continuous function of a function with temperate growth multiplied by
the Bessel potential. -/
def besselPotentialFunSMul {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) : E →ᵇ ℂ :=
  ofNormedAddCommGroup (fun x ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2) • g x) ?_ C ?_
where finally
  · have : Function.HasTemperateGrowth (fun x ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2) • g x) := by fun_prop
    exact this.1.continuous
  · intro x
    specialize hg₂ x
    simp only [Complex.real_smul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_eq_self.mpr (by positivity), neg_div, Real.rpow_neg (by positivity)]
    field_simp
    rwa [mul_comm]

theorem coe_besselPotentialFunSMul {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) :
    (besselPotentialFunSMul s C hg₁ hg₂ : E → ℂ) = (fun x ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2) • g x) := rfl

@[fun_prop]
theorem hasTemperateGrowth_besselPotentialFunSMul {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) :
    (besselPotentialFunSMul s C hg₁ hg₂ : E → ℂ).HasTemperateGrowth := by
  rw [coe_besselPotentialFunSMul]
  fun_prop

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace BoundedContinuousFunction

/-- Multiplication with a bounded function is a continuous linear map on `Lp` functions. -/
def holderL (g : E →ᵇ ℂ) : Lp F p (volume : Measure E) →L[ℂ] Lp F p (volume : Measure E) :=
    (ContinuousLinearMap.lsmul ℂ ℂ).holderL volume ⊤ p p (g.memLp_top.toLp)

@[simp]
theorem holderL_apply (g : E →ᵇ ℂ) (f : Lp F p (volume : Measure E)) :
    g.holderL f = g.memLp_top.toLp _ (μ := volume) • f := by
  rfl

theorem holderL_ae (g : E →ᵇ ℂ) (f : Lp F p (volume : Measure E)) :
    g.holderL f =ᵐ[volume] fun x ↦ g x • f x := by
  rw [holderL_apply]
  have : ∞.HolderTriple p p := by infer_instance
  filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (hpqr := this) g.memLp_top.toLp f,
    g.memLp_top.coeFn_toLp] with x hfg hg
  simp [hfg, hg]

end BoundedContinuousFunction

end BCF

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable {s : ℝ}

-- define the function as an `Lp` function (complex-valued)

theorem _root_.MeasureTheory.Lp.memLp_rpow_add_sq_norm (hs : Module.finrank ℝ E < 2 * s) :
    MemLp (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
  have : AEStronglyMeasurable (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)) := by
    have : (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by fun_prop
    exact this.1.continuous.aestronglyMeasurable
  nth_rw 1 [memLp_iff]
  rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (by norm_num) (by norm_num) this]
  suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← eNorm_pow]
    convert h using 4
    rw [← Real.rpow_mul_natCast (by positivity)]
    simp
  apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

theorem _root_.MeasureTheory.Lp.memLp_ofReal_rpow_add_sq_norm (hs : Module.finrank ℝ E < 2 * s) :
    MemLp (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) 2 := by
  apply (memLp_rpow_add_sq_norm hs).ofReal

end Lp

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F]

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap

section normed

variable [NormedSpace ℂ F]

variable {s s' : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

open ContinuousLinearMap

variable (F) in
/-- A Schwartz function defines a continuous linear map from `Lp` to `F` via integration. -/
def _root_.SchwartzMap.toLpFunctional (f : 𝓢(E, ℂ)) : Lp F p (volume : Measure E) →L[ℂ] F :=
  haveI := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  haveI : Fact (1 ≤ (1 - p⁻¹)⁻¹) := by simp [fact_iff]
  (lsmul ℂ ℂ).lpPairing (volume : Measure E) (1 - p⁻¹)⁻¹ p (f.toLp _)

@[simp]
theorem _root_.SchwartzMap.toLpFunctional_apply (f : 𝓢(E, ℂ)) (g : Lp F p) :
    f.toLpFunctional F g = ∫ x, f x • g x := by
  rw [SchwartzMap.toLpFunctional, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (1 - p⁻¹)⁻¹] with x hf
  simp [hf]

namespace BesselPotentialSpace

theorem toLp_eq_toDistr_of_eq_zero {f : H^{s, p}(E, F)} (hs : s = 0) :
    f.toLp = f.toDistr := by
  simp [← besselPotential_neg_toLp_eq, hs]

theorem toDistr_apply (f : H^{s, p}(E, F)) (u : 𝓢(E, ℂ)) :
    f.toDistr u = (𝓕 <| 𝓕⁻ u |>.smulLeftCLM ℂ fun x ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)).toLpFunctional F
      f.toLp := by
  rw [SchwartzMap.toLpFunctional_apply, ← besselPotential_neg_toLp_eq]
  rw [besselPotential]
  simp only [fourierMultiplierCLM_apply_apply, Lp.toTemperedDistribution_apply]
  congr
  ext x
  congr 3
  apply SchwartzMap.smulLeftCLM_ofReal
  exact Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-s / 2)

variable (E F s p) in
/-- The map from Sobolev functions `H^{s,p}` to `𝓢'` as a continuous linear map. -/
def toTemperedDistributionCLM : H^{s, p}(E, F) →L[ℂ] 𝓢'(E, F) where
  toFun f := f.toDistr
  map_add' := toDistr_add
  map_smul' := toDistr_smul
  cont := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro g
    simp_rw [toDistr_apply]
    apply Continuous.comp
    · fun_prop
    · convert (toLpₗᵢ E F s p).continuous
      ext
      simp

end BesselPotentialSpace

namespace SchwartzMap

open scoped BesselPotentialSpace

variable {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

variable (E F s p) in
/-- The embedding of Schwartz functions into the Sobolev space. -/
def toBesselPotentialSpace : 𝓢(E, F) →L[ℂ] H^{s, p}(E, F) :=
  (BesselPotentialSpace.toLpₗᵢ E F s p).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
  toLpCLM ℂ F p (volume : Measure E) ∘L
  SchwartzMap.fourierMultiplierCLM F (fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2)))

theorem toBesselPotentialSpace_apply (f : 𝓢(E, F)) :
  f.toBesselPotentialSpace E F s p = BesselPotentialSpace.ofLp s ((f.fourierMultiplierCLM F
    (fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2)))).toLp p) := by rfl

@[simp]
theorem toDistr_toBesselPotentialSpace (f : 𝓢(E, F)) :
    (f.toBesselPotentialSpace E F s p).toDistr = f := by
  rw [toBesselPotentialSpace_apply, BesselPotentialSpace.toDistr_ofLp,
    Lp.toTemperedDistribution_toLp_eq,
    ← fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop), ← besselPotential]
  simp

theorem toBesselPotentialSpace_eq_toLp_of_eq_zero (f : 𝓢(E, F)) (hs : s = 0) :
    (f.toBesselPotentialSpace E F s p).toLp = f.toLp p := by
  simp [toBesselPotentialSpace_apply, hs]

theorem norm_toBesselPotentialSpace (f : 𝓢(E, F)) :
    ‖f.toBesselPotentialSpace E F s p‖ = ‖f.fourierMultiplierCLM F
    (fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2))) |>.toLp p‖ := by
  simp [toBesselPotentialSpace_apply, ← BesselPotentialSpace.norm_toLp_eq]

attribute [fun_prop] denseRange_toLpCLM LinearIsometryEquiv.surjective

variable (E F s) in
@[fun_prop]
theorem denseRange_toBesselPotentialSpace (hp : p ≠ ⊤) :
    DenseRange (toBesselPotentialSpace E F s p) := by
  simp only [toBesselPotentialSpace, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv]
  suffices Function.Surjective (fourierMultiplierCLM F
      fun x ↦ Complex.ofReal <| (1 + ‖x‖ ^ 2) ^ (s / 2)) by fun_prop
  intro f
  use f.fourierMultiplierCLM F (fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ))
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  convert DFunLike.ext_iff.mp (fourierMultiplierCLM_const (1 : ℂ)) f
  · rw [Pi.mul_apply]
    norm_cast
    rw [← Real.rpow_add (by positivity)]
    ring_nf
    simp
  · simp

end SchwartzMap

end normed

section inner

variable [InnerProductSpace ℂ F]

namespace BesselPotentialSpace

section BCF

open BoundedContinuousFunction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem toTemperedDistribution_holderL {g : E →ᵇ ℂ} (hg : (g : E → ℂ).HasTemperateGrowth)
    (f : Lp F p (volume : Measure E)) :
    Lp.toTemperedDistribution (g.holderL f) = smulLeftCLM F g f := by
  rwa [holderL_apply, MeasureTheory.Lp.toTemperedDistribution_smul_eq]

theorem fourierInv_toTemperedDistribution_holderL_fourier {g : E →ᵇ ℂ}
    (hg : (g : E → ℂ).HasTemperateGrowth) (f : Lp F 2 (volume : Measure E)) :
    𝓕⁻ (Lp.toTemperedDistribution <| g.holderL <| 𝓕 f) =
      fourierMultiplierCLM F g f := by
  rw [toTemperedDistribution_holderL hg, ← Lp.fourier_toTemperedDistribution_eq]
  rw [fourierMultiplierCLM_apply]

theorem fourierInv_toTemperedDistribution_holderL_besselPotentialFunSMul_fourier {g : E → ℂ}
    (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) (f : Lp F 2 (volume : Measure E)) :
    𝓕⁻ (Lp.toTemperedDistribution <| (besselPotentialFunSMul s C hg₁ hg₂).holderL <| 𝓕 f) =
      besselPotential E F (-s) (fourierMultiplierCLM F g f) := by
  rw [fourierInv_toTemperedDistribution_holderL_fourier (by fun_prop)]
  rw [besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ (by fun_prop)]
  congr
  ext x
  simp [coe_besselPotentialFunSMul, mul_comm]

end BCF

variable {s : ℝ}

/-- Fourier multiplier as a continuous linear map from `H^{s}` to `H^{s'}`. -/
@[no_expose]
def fourierMultiplierCLM (s s' C : ℝ) (g : E → ℂ)
    (hg₁ : g.HasTemperateGrowth) (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2)) :
    H^{s}(E, F) →L[ℂ] H^{s'}(E, F) :=
  ((toLpₗᵢ E F s' 2).trans (Lp.fourierTransformₗᵢ E F)
    |>.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
  (besselPotentialFunSMul (s - s') C hg₁ hg₂).holderL ∘L
  ((toLpₗᵢ E F s 2).trans (Lp.fourierTransformₗᵢ E F)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
private
theorem fourierMultiplierCLM_toLp {s : ℝ} (s' C : ℝ) {g : E → ℂ} (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2)) (f : H^{s}(E, F)) :
    (f.fourierMultiplierCLM s s' C g hg₁ hg₂).toLp =
    𝓕⁻ ((besselPotentialFunSMul (s - s') C hg₁ hg₂).holderL (𝓕 f.toLp)) :=
  rfl

@[simp]
theorem fourierMultiplierCLM_toDistr {s : ℝ} (s' C : ℝ) {g : E → ℂ} (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2)) (f : H^{s}(E, F)) :
    (f.fourierMultiplierCLM s s' C g hg₁ hg₂).toDistr = f.toDistr.fourierMultiplierCLM F g := by
  rw [← besselPotential_neg_toLp_eq, fourierMultiplierCLM_toLp,
    ← Lp.fourierInv_toTemperedDistribution_eq,
    fourierInv_toTemperedDistribution_holderL_besselPotentialFunSMul_fourier,
    besselPotential_besselPotential_apply, ← besselPotential_neg_toLp_eq,
    besselPotential_fourierMultiplierCLM_comm _ hg₁]
  ring_nf

variable (E F) in
/-- Monotonicity -/
@[no_expose]
def mono (s s' : ℝ) :
    H^{s}(E, F) →L[ℂ] H^{s'}(E, F) :=
  if h : s' ≤ s then
    fourierMultiplierCLM s s' 1 (fun _ ↦ 1) (by fun_prop) (fun _ ↦ ?_)
  else
    0
where finally
  simp only [one_mem, CStarRing.norm_of_mem_unitary, one_mul]
  exact Real.one_le_rpow (by simp) (by grind)

variable {s' : ℝ}

theorem toDistr_mono (h : s' ≤ s) (f : H^{s}(E, F)) : (f.mono E F s s').toDistr = f.toDistr := by
  simp [mono, h]

theorem _root_.SchwartzMap.toBesselPotentialSpace_mono (f : 𝓢(E, F)) (s s' : ℝ) (hs : s' ≤ s) :
    (f.toBesselPotentialSpace E F s 2).mono E F s s' = f.toBesselPotentialSpace E F s' 2 := by
  ext
  simp [toDistr_mono hs]

theorem mono_injective (h : s' ≤ s) : Function.Injective (BesselPotentialSpace.mono E F s s') := by
  intro f₁ f₂ hf
  ext u
  simp [← toDistr_mono h, hf]

@[fun_prop]
theorem denseRange_mono (h : s' ≤ s) : DenseRange (BesselPotentialSpace.mono E F s s') := by
  suffices DenseRange (BesselPotentialSpace.mono E F s s' ∘
    SchwartzMap.toBesselPotentialSpace E F s 2) from this.of_comp
  convert SchwartzMap.denseRange_toBesselPotentialSpace E F s' (p := 2) (by simp)
  ext f : 1
  simp [f.toBesselPotentialSpace_mono _ _ h]

theorem mono_apply_eq_zero_of_lt (h : s < s') (f : H^{s}(E, F)) :
    (f.mono E F s s').toDistr = 0 := by
  have h : ¬ s' ≤ s := by grind
  simp [mono, h]

open LineDeriv Laplacian Real

variable (F) in
/-- Partial derivative -/
def lineDerivOp (s : ℝ) (m : E) : H^{s}(E, F) →L[ℂ] H^{s - 1}(E, F) :=
  (2 * π * Complex.I) • (fourierMultiplierCLM s (s - 1) ‖m‖ (fun x ↦ Complex.ofReal <| inner ℝ x m)
    ?_ ?_)
where finally
  · fun_prop
  · intro x
    simp only [Complex.norm_real, norm_eq_abs, _root_.sub_sub_cancel, one_div]
    grw [abs_real_inner_le_norm]
    rw [mul_comm]
    gcongr
    apply le_of_sq_le_sq _ (by positivity)
    calc
      _ ≤ 1 + ‖x‖ ^ 2 := by simp
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp

instance instLineDeriv (s : ℝ) : LineDeriv E H^{s}(E, F) H^{s - 1}(E, F) where
  lineDerivOp m f := f.lineDerivOp F s m

@[simp]
theorem lineDerivOp_apply (m : E) (f : H^{s}(E, F)) : f.lineDerivOp F s m = ∂_{m} f := rfl

@[simp]
theorem toDistr_lineDerivOp (m : E) {s : ℝ} (f : H^{s}(E, F)) :
    (∂_{m} f).toDistr = ∂_{m} f.toDistr := by
  rw [← lineDerivOp_apply, lineDerivOp, smul_apply,
    toDistr_smul, fourierMultiplierCLM_toDistr,
    lineDeriv_eq_fourierMultiplierCLM]

variable (E F) in
/-- The laplacian -/
def laplacian (s : ℝ) : H^{s}(E, F) →L[ℂ] H^{s - 2}(E, F) :=
  (Complex.ofReal <| -(2 * π) ^ 2) • (fourierMultiplierCLM s (s - 2) 1
    (fun x ↦ Complex.ofReal <| ‖x‖ ^ 2) ?_ ?_)
where finally
  · fun_prop
  · simp

instance instLaplacian (s : ℝ) : Laplacian H^{s}(E, F) H^{s - 2}(E, F) where
  laplacian f := f.laplacian E F s

@[simp]
theorem laplacian_apply (f : H^{s}(E, F)) : f.laplacian E F s = Δ f := rfl

example (f : H^{2}(E, F)) (g : H^{0}(E, F)) (h : (Δ f).toDistr = g.toDistr) :
    (Δ f).copy 0 = g := by
  ext : 1
  simpa

@[simp]
theorem toDistr_laplacian {s : ℝ} (f : H^{s}(E, F)) : (Δ f).toDistr = Δ f.toDistr := by
  rw [← laplacian_apply, laplacian, smul_apply,
    toDistr_smul, fourierMultiplierCLM_toDistr,
    laplacian_eq_fourierMultiplierCLM]
  norm_cast

theorem _root_.SchwartzMap.toBesselPotentialSpace_laplacian (f : 𝓢(E, F)) :
    (Δ f).toBesselPotentialSpace E F (s - 2) 2 = Δ (f.toBesselPotentialSpace E F s 2) := by
  ext : 1
  simp

end BesselPotentialSpace

end inner
