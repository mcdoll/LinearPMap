/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import LinearPMap.Analysis.InnerProductSpace.LinearPMap

/-! # Concrete unbounded operators -/

@[expose] public noncomputable section

open RCLike LinearPMap WithLp

open scoped ComplexConjugate

variable {𝕜 𝕜₂ D E E' Eₗ F : Type*}

variable [RCLike 𝕜]

section definition

variable [RCLike 𝕜] [RCLike 𝕜₂]

variable {σ : 𝕜 →+* 𝕜₂}


variable {D E E' Eₗ F : Type*}
variable [AddCommGroup D] [Module 𝕜 D]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜₂ F]

variable (σ D E F) in
/-- A `ConcreteLinearPMap` is a tuple of a linear map `D →ₗ[𝕜] F` and a linear map `D →ₗ[𝕜] E`,
where the later acts an embedding (and hence is assumed to be injective). -/
structure ConcreteLinearPMap where
  /-- The underlying map -/
  toFun : D →ₛₗ[σ] F
  /-- The embedding of the domain -/
  emb : D →ₗ[𝕜] E
  inj : Function.Injective emb

end definition

namespace ConcreteLinearPMap

section LinearAlgebra

variable [RCLike 𝕜₂]

variable [AddCommGroup D] [Module 𝕜 D]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜₂ F]
variable {σ : 𝕜 →+* 𝕜₂}

variable {f : ConcreteLinearPMap σ D E F}

variable (f) in
/-- Define an unbounded operator from a linear operator and an embedding. -/
def toLinearPMap : E →ₛₗ.[σ] F where
  domain := f.emb.range
  toFun := f.toFun ∘ₛₗ (LinearEquiv.ofInjective f.emb f.inj).symm.toLinearMap

@[simp]
theorem toLinearPMap_domain : f.toLinearPMap.domain = f.emb.range := rfl

@[simp]
theorem toLinearPMap_apply (x : D) : f.toLinearPMap ⟨f.emb x, by simp⟩ = f.toFun x := by
  simp only [toLinearPMap, mk_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  congr
  rw [LinearEquiv.symm_apply_eq]
  ext
  simp

theorem toLinearPMap_exists_of_mem_domain (x : E) (hx : x ∈ f.toLinearPMap.domain) :
    ∃ y : D, f.emb y = x ∧ f.toLinearPMap ⟨x, hx⟩ = f.toFun y := by
  rw [toLinearPMap_domain, LinearMap.mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  use y, hy
  convert toLinearPMap_apply y
  rw [← hy]

theorem toLinearPMap_exists (x : f.toLinearPMap.domain) :
    ∃ y : D, f.emb y = x ∧ f.toLinearPMap x = f.toFun y :=
  toLinearPMap_exists_of_mem_domain x.val x.prop

variable (f) in
theorem dense_domain_toLinearPMap_iff [TopologicalSpace E] :
    Dense (f.toLinearPMap.domain : Set E) ↔ DenseRange f.emb := by
  rfl

end LinearAlgebra

section InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open scoped InnerProductSpace

open Filter
open scoped Topology

variable [AddCommGroup D] [Module 𝕜 D]
variable {f : ConcreteLinearPMap (RingHom.id 𝕜) D E E}

theorem isSymmetric_toLinearPMap (h : ∀ x y, ⟪f.toFun x, f.emb y⟫_𝕜 = ⟪f.emb x, f.toFun y⟫_𝕜) :
    IsSymmetric f.toLinearPMap := by
  intro x y
  obtain ⟨x', hx', hx⟩ := ConcreteLinearPMap.toLinearPMap_exists x
  obtain ⟨y', hy', hy⟩ := ConcreteLinearPMap.toLinearPMap_exists y
  grind

end InnerProductSpace

section ComplexInnerProductSpace

variable [AddCommGroup D] [Module ℂ D]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {f : ConcreteLinearPMap (RingHom.id ℂ) D E E}

theorem isSelfAdjoint_toLinearPMap_of_surjective (hf : f.toLinearPMap.IsSymmetric)
    (hf' : DenseRange f.emb)
    (h : ∀ y (c : ℝ), c ≠ 0 → ∃ x : D, c • Complex.I • f.emb x + f.toFun x = y) :
    IsSelfAdjoint f.toLinearPMap := by
  apply isSelfAdjoint_of_surjective hf hf'
  intro x c hc
  obtain ⟨y, hy⟩ := h x c hc
  use ⟨f.emb y, by simp⟩
  grind [ConcreteLinearPMap.toLinearPMap_apply]

end ComplexInnerProductSpace

end ConcreteLinearPMap
