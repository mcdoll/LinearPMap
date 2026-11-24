/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import LinearPMap.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Analysis.Normed.Operator.Banach

/-! # Inverses as continuous linear maps -/

@[expose] public noncomputable section

variable {R 𝕜 D E E' Eₗ F : Type*}

namespace LinearPMap

section Topology

variable [CommRing R]

variable [AddCommGroup E] [Module R E] [TopologicalSpace E]
variable [AddCommGroup F] [Module R F] [TopologicalSpace F]

variable {f : E →ₗ.[R] F}

open Filter
open scoped Topology

section Neg

theorem IsClosed.neg [ContinuousNeg F] (hf : f.IsClosed) : (-f).IsClosed := by
  unfold IsClosed at hf ⊢
  rw [neg_graph f]
  simp only [Submodule.map_coe, LinearMap.prodMap_apply, LinearMap.id_coe, id_eq,
    LinearMap.neg_apply]
  rw [← Topology.IsClosedEmbedding.isClosed_iff_image_isClosed]
  · exact hf
  · apply Topology.IsClosedEmbedding.id.prodMap (Homeomorph.neg F).isHomeomorph.isClosedEmbedding

end Neg

section SequentialSpace

variable [SequentialSpace (E × F)]

theorem isClosed_iff_seq :
    f.IsClosed ↔ ∀ (a : ℕ → f.domain) (a₀ : E) (y₀ : F),
    Tendsto ((↑) ∘ a) atTop (𝓝 a₀) → Tendsto (f ∘ a) atTop (𝓝 y₀) →
    ∃ (ha₀ : a₀ ∈ f.domain), f ⟨a₀, ha₀⟩ = y₀ := by
  unfold IsClosed
  rw [← isSeqClosed_iff_isClosed, IsSeqClosed]
  constructor
  · intro h a a₀ y₀ ha hTa
    simpa using h (by intro; simp) (Filter.Tendsto.prodMk_nhds ha hTa)
  · intro h a ⟨a₀, y₀⟩ ha ha₀
    simp only [SetLike.mem_coe, mem_graph_iff, Subtype.exists, exists_and_left,
      exists_eq_left] at ha ⊢
    choose ha ha' using ha
    apply h (fun n ↦ ⟨(a n).1, ha n⟩) a₀ y₀
    · exact ha₀.fst_nhds
    · convert ha₀.snd_nhds
      simp [ha']

theorem _root_.LinearMap.isClosed_toLinearPMap [T2Space F] {g : E →ₗ[R] F} (hg : Continuous g) :
    (g.toPMap ⊤).IsClosed := by
  rw [isClosed_iff_seq] at ⊢
  intro a a₀ y₀ ha₀ hy₀
  suffices g a₀ = y₀ by simp [this]
  exact tendsto_nhds_unique ((hg.tendsto a₀).comp ha₀) hy₀

theorem IsClosed.vadd' [ContinuousSub F] {f : E →ₗ.[R] F} (hf : f.IsClosed) {g : E →ₗ[R] F}
    (hg : Continuous g) :
    (g +ᵥ f).IsClosed := by
  rw [isClosed_iff_seq] at hf ⊢
  intro a a₀ y₀ ha₀ hy₀
  have h' : Tendsto (↑f ∘ a) atTop (𝓝 (y₀ - g a₀)) := by
    convert hy₀.sub ((hg.tendsto a₀).comp ha₀)
    simp
  obtain ⟨ha₀', h''⟩ := hf a a₀ (y₀ - g a₀) ha₀ h'
  use ha₀'
  simp [h'']

theorem IsClosed.vadd [ContinuousSub F] {f : E →ₗ.[R] F} (hf : f.IsClosed) (g : E →L[R] F) :
    (g.toLinearMap +ᵥ f).IsClosed :=
  hf.vadd' g.continuous

end SequentialSpace

variable [ContinuousAdd E] [ContinuousAdd F]
variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

theorem IsClosed.closure_eq (hT : f.IsClosed) : f.closure = f := by
  apply eq_of_eq_graph
  rw [← hT.isClosable.graph_closure_eq_closure_graph, hT.submodule_topologicalClosure_eq]


end Topology


section Topology

variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

variable {f : E →ₗ.[𝕜] F}

attribute [grind .] Function.Bijective.injective

/-- If `f` is bijective and closed, then the inverse is defined as a continuous linear map. -/
def inverseCLM (hf : Function.Bijective f) (hf' : f.IsClosed) : F →L[𝕜] E :=
  ContinuousLinearMap.ofIsClosedGraph (g := inverseLM hf) ?_
where finally
  rw [inverseLM_graph, inverse_graph (by grind)]
  exact (Homeomorph.prodComm E F).isClosed_image.mpr hf'

section resolvent

variable {f g : E →ₗ.[𝕜] E} {z z₁ z₂ : 𝕜}

variable [SMulCommClass 𝕜 𝕜 E]

open Classical in
/-- The resolvent of a `LinearPMap` as a `LinearMap`.

This definition is only used to deduce algebraic properties, which hold without any reference to
the topology. In particular, we prove the first and second resolvent identity.
-/
noncomputable def resolventCLM (f : E →ₗ.[𝕜] E) (z : 𝕜) : E →L[𝕜] E :=
  if hz : z ∈ f.resolventSet ∧ f.IsClosed then
    (z • LinearMap.id +ᵥ (-f) : E →ₗ.[𝕜] E).inverseCLM hz.1 ?_
  else 0
where finally
  apply hz.2.neg.vadd'
  simp only [LinearMap.coe_smul, LinearMap.id_coe]
  fun_prop

theorem coe_resolventCLM (hf : IsClosed f) : f.resolventCLM z = f.resolventLM z := by
  by_cases hz : z ∈ f.resolventSet
  · simp [resolventCLM, hf, hz, resolventLM]
    rfl
  · simp [resolventCLM, resolventLM, hz]

theorem resolventCLM_apply (hf : IsClosed f) (x : E) : f.resolventCLM z x = f.resolventLM z x := by
  simp [← coe_resolventCLM hf]

/-- The range of the resolvent `R(f, z)` is equal to the domain of `f` for any `z` in the resolvent
set. -/
theorem range_resolventCLM (hf : IsClosed f) (hz : z ∈ f.resolventSet) :
    (f.resolventCLM z).range = f.domain := by
  rw [coe_resolventCLM hf]
  exact range_resolventLM f hz

/-- The first resolvent identity. -/
theorem resolventCLM_sub_resolventLM_eq (hf : IsClosed f) (hz₁ : z₁ ∈ f.resolventSet)
    (hz₂ : z₂ ∈ f.resolventSet) :
    f.resolventCLM z₁ - f.resolventCLM z₂ = (z₂ - z₁) • f.resolventCLM z₁ ∘L f.resolventCLM z₂ := by
  apply ContinuousLinearMap.coe_injective
  simpa [coe_resolventCLM hf] using resolventLM_sub_resolventLM_eq hz₁ hz₂

theorem resolventCLM_commute (hf : IsClosed f) (hz₁ : z₁ ∈ f.resolventSet)
    (hz₂ : z₂ ∈ f.resolventSet) :
    f.resolventCLM z₁ ∘L f.resolventCLM z₂ = f.resolventCLM z₂ ∘L f.resolventCLM z₁ := by
  apply ContinuousLinearMap.coe_injective
  simpa [coe_resolventCLM hf] using resolventLM_commute hz₁ hz₂

end resolvent

end Topology

end LinearPMap
