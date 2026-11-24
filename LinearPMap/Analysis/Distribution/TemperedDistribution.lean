/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-! # Tempered distributions -/

@[expose] public noncomputable section

open SchwartzMap ContinuousLinearMap MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {ι 𝕜 E F F₁ F₂ : Type*}

namespace MeasureTheory.Measure

open TemperedDistribution

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E) [hμ : μ.HasTemperateGrowth]

theorem smulLeftCLM_toTemperedDistribution {f : E → ℂ} (hf : f.HasTemperateGrowth) :
    smulLeftCLM ℂ f μ.toTemperedDistribution = hf.toTemperedDistribution μ := by
  ext u
  simp [SchwartzMap.smulLeftCLM_apply hf, mul_comm]


end MeasureTheory.Measure

namespace MeasureTheory.Lp

open scoped ENNReal TemperedDistribution

variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [CompleteSpace F]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

variable (E F)
theorem toTemperedDistribution_injective (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [Fact (1 ≤ p)] [μ.HasTemperateGrowth] [IsLocallyFiniteMeasure μ] :
    Function.Injective (toTemperedDistribution (F := F) (p := p) (μ := μ)) :=
  LinearMap.ker_eq_bot.mp MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot

end MeasureTheory.Lp
