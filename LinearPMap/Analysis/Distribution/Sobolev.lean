/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.Sobolev

/-! # Sobolev spaces (Bessel potential spaces)

In this file we define Sobolev spaces on normed vector spaces via the Fourier transform.
These spaces are also known as Bessel potential spaces. The Bessel potential operator
`besselPotential` is the Fourier multiplier with the symbol `x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)` and a
tempered distribution `u` belongs to the Sobolev space `H^{s,p}` if
`besselPotential E F s u` can be represented by a `Lp` function, informally this is written as
`𝓕⁻ (fun x ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)) 𝓕 u ∈ Lp`.

Note that the Bessel potential is the operator `(1 - (2 * π) ^ (-2) • Δ) ^ (s / 2)` and not
`(1 - Δ) ^ (s / 2)` due to the convention of the Fourier transform. This obviously does not impact
the definition of the Sobolev spaces.

## Main definitions

* `TemperedDistribution.besselPotential`: The Bessel potential operator is the Fourier multiplier
  with the function `(1 + ‖x‖ ^ 2) ^ (s / 2)`.
* `TemperedDistribution.memSobolev`: A tempered distribution lies in the Sobolev space of order `s`
  and `p` if `besselPotential E F s u ∈ Lp`.

## Main statements

* `SchwartzMap.memSobolev`: Each Schwartz function belongs to every Sobolev space
* `TemperedDistribution.memSobolev_two_iff_fourier`: The characterization of `p = 2` Sobolev
  functions
* `TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`: If `u` is a Sobolev
  function, then `g • u` is a Sobolev function of the same order provided `g` is bounded.
* `TemperedDistribution.MemSobolev.lineDerivOp`: If `u` is a Sobolev function of order `s`, then
  `∂_{m} u` is a Sobolev function of order `s - 1`.
* `TemperedDistribution.MemSobolev.laplacian`: If `u` is a Sobolev function of order `s`, then
  `Δ u` is a Sobolev function of order `s - 2`.


-/

@[expose] public noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap

namespace TemperedDistribution

section normed

variable [NormedSpace ℂ F]

theorem fourierMultiplierCLM_comm {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₁ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g₁ (fourierMultiplierCLM F g₂ f) =
      fourierMultiplierCLM F g₂ (fourierMultiplierCLM F g₁ f) := by
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  rw [mul_comm]

theorem besselPotential_fourierMultiplierCLM_comm (s : ℝ) {g : E → ℂ} (hg₁ : g.HasTemperateGrowth)
    (f : 𝓢'(E, F)) :
    besselPotential E F s (fourierMultiplierCLM F g f) =
      fourierMultiplierCLM F g (besselPotential E F s f) := by
  rw [besselPotential, fourierMultiplierCLM_comm (by fun_prop) (by fun_prop)]

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A tempered distribution belongs to the Sobolev space of order `s` and `p = 2` if and only if
its Fourier transform multiplied by `(1 + ‖x‖ ^ 2) ^ (s / 2)` is in `Lp`. -/
theorem memSobolev_two_iff_fourier {s : ℝ} {f : 𝓢'(E, F)} :
    MemSobolev s 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)),
    smulLeftCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f) = f' := by
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hf'
    rw [hf', Lp.fourier_toTemperedDistribution_eq f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [besselPotential, TemperedDistribution.fourierMultiplierCLM_apply]
    apply_fun 𝓕⁻ at hf'
    rw [hf', Lp.fourierInv_toTemperedDistribution_eq f']

theorem memSobolev_zero_two_iff_fourier {f : 𝓢'(E, F)} :
    MemSobolev 0 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)), 𝓕 f = f' := by
  simp [memSobolev_two_iff_fourier]

open scoped BoundedContinuousFunction

section LineDeriv

open scoped LineDeriv Laplacian Real

end LineDeriv

end inner

end TemperedDistribution
