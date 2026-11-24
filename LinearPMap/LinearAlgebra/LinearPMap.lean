/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.GroupTheory.GroupAction.Basic

/-! # Resolvent of an unbounded operator -/

@[expose] public noncomputable section

open LinearPMap

variable {R 𝕜 D E E' Eₗ F G : Type*}

namespace LinearPMap

section LinearAlgebra

variable [CommRing R]

variable [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]
variable [AddCommGroup G] [Module R G]
variable {f : E →ₗ.[R] F}

attribute [grind _=_] LinearPMap.ker_eq_bot

section CompLinearMap

open Classical in
/-- Composition of a `LinearPMap` with a `LinearMap`.

The composition is well-defined if the range of the `LinearMap` is
contained in the domain of the `LinearPMap`.
Otherwise it takes the junk value `0`. -/
noncomputable def compLinearMap (f : F →ₗ.[R] G) (g : E →ₗ[R] F) :
    E →ₗ[R] G :=
  if hgf : LinearMap.range g ≤ f.domain then f.toFun.comp (g.codRestrict f.domain
    (hgf <| LinearMap.mem_range_self g ·)) else 0

theorem compLinearMap_apply {f : F →ₗ.[R] G} {g : E →ₗ[R] F}
    (hgf : LinearMap.range g ≤ f.domain) (x : E) :
    (f.compLinearMap g) x = f ⟨g x, hgf (LinearMap.mem_range_self g x)⟩ := by
  simp [compLinearMap, hgf]
  congr

end CompLinearMap

section Injective

theorem graph_eq_map_graph_inverse (hf : f.ker = ⊥) :
    f.graph = f.inverse.graph.map (LinearEquiv.prodComm R F E : (F × E) →ₗ[R] (E × F)) := by
  rw [inverse_graph hf]
  ext x
  simp

attribute [grind .] LinearPMap.mem_inverse_graph

theorem mem_graph_of_inverse (hf : f.ker = ⊥) (y : f.inverse.domain) :
    (f.inverse y, (y : F)) ∈ f.graph := by
  simp [graph_eq_map_graph_inverse hf]

end Injective

section Bijective

theorem inverse_domain_eq_top_of_bijective (hf : Function.Bijective f) :
    f.inverse.domain = ⊤ := by
  rw [inverse_domain, LinearMap.range_eq_top]
  exact hf.2

theorem mem_inverse_domain_of_bijective (hf : Function.Bijective f) (y : F) :
    y ∈ f.inverse.domain := by
  rw [inverse_domain_eq_top_of_bijective hf]
  exact Submodule.mem_top

open Classical in
/-- If `f` is bijective, then the inverse is defined as a linear map. -/
noncomputable def inverseLM (hf : Function.Bijective f) : F →ₗ[R] E :=
  f.inverse.toFun.comp (LinearEquiv.ofTop f.inverse.domain
    (inverse_domain_eq_top_of_bijective hf)).symm.toLinearMap

theorem inverseLM_apply_eq_inverse_apply (hf : Function.Bijective f) {y : F} :
    f.inverseLM hf y = f.inverse ⟨y, mem_inverse_domain_of_bijective hf y⟩ := by
  simp only [inverseLM, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    toFun_eq_coe]
  congr

@[simp]
theorem inverseLM_graph (hf : Function.Bijective f) : (inverseLM hf).graph = f.inverse.graph := by
  ext ⟨x, y⟩
  simp [inverseLM_apply_eq_inverse_apply]
  grind

theorem inverseLM_eq_if_range_eq_top (hf : Function.Bijective f) :
  inverseLM hf = f.inverse.toFun.comp (LinearEquiv.ofTop f.inverse.domain
    (inverse_domain_eq_top_of_bijective hf)).symm.toLinearMap := rfl

@[grind _=_]
theorem inverseLM_range (hf : Function.Bijective f) :
    (f.inverseLM hf).range = f.domain := by
  simp [inverseLM_eq_if_range_eq_top hf, inverse_range (LinearPMap.ker_eq_bot.mpr hf.1)]

theorem inverseLM_apply_mem_domain (hf : Function.Bijective f) (x : F) :
    f.inverseLM hf x ∈ f.domain := by
  grind [LinearMap.mem_range_self]

@[grind .]
theorem mem_graph_of_inverseLM (hf : Function.Bijective f) (y : F) :
    (f.inverseLM hf y, y) ∈ f.graph := by
  grind [inverseLM_apply_eq_inverse_apply, LinearPMap.mem_graph_of_inverse, hf.1]

theorem inverseLM_apply_apply_cancel (hf : Function.Bijective f) (x : F) :
    f ⟨f.inverseLM hf x, inverseLM_apply_mem_domain hf x⟩ = x := by
  apply ((image_iff (inverseLM_apply_mem_domain hf x)).mpr ?_).symm
  grind

theorem apply_inverseLM_apply_cancel (hf : Function.Bijective f) (x' : f.domain) :
    f.inverseLM hf (f x') = x' := by
  have : (f x', (x' : E)) ∈ f.inverse.graph := by grind [hf.1]
  rw [← image_iff (mem_inverse_domain_of_bijective hf _)] at this
  grind [inverseLM_apply_eq_inverse_apply]

/-- Calculate the difference of inverses of `LinearPMap`s `f` and `g` assuming both are bijective
and the domain of `g` is contained in the domain of `f`.

Informally, this is expressed as `f⁻¹ - g⁻¹ = f⁻¹ (f - g) g⁻¹`. -/
theorem inverseLM_sub_inverseLM_eq {g : E →ₗ.[R] F} (hf : Function.Bijective f)
    (hg : Function.Bijective g) (hfg : g.domain ≤ f.domain) :
    f.inverseLM hf - g.inverseLM hg =
      f.inverseLM hf ∘ₗ ((g - f).compLinearMap (g.inverseLM hg)) := by
  ext x
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply]
  rw [compLinearMap_apply (by simpa [sub_domain, inverseLM_range hg] using hfg), sub_apply]
  simp [inverseLM_apply_apply_cancel hg, apply_inverseLM_apply_cancel hf]

end Bijective

section resolvent

variable {f : E →ₗ.[R] E} {r : R}

variable [SMulCommClass R R E]


/-- The resolvent set of a `LinearPMap`.

This definition only agrees with the conventional one only if `f` is closed, but if that is not
the case, then the conventional definition yields that `resolvent_set f = ⊤`
We use this definition for convenience and since it makes fewer assumptions. -/
def resolventSet (f : E →ₗ.[R] E) : Set R :=
  { z | (z • LinearMap.id (R := R) (M := E) +ᵥ (-f) : f.domain → E).Bijective }

open Classical in
/-- The resolvent of a `LinearPMap` as a `LinearMap`.

This definition is only used to deduce algebraic properties, which hold without any reference to
the topology. In particular, we prove the first and second resolvent identity.
-/
noncomputable def resolventLM (f : E →ₗ.[R] E) (z : R) : E →ₗ[R] E :=
    if hz : z ∈ resolventSet f then
      (z • LinearMap.id +ᵥ (-f) : E →ₗ.[R] E).inverseLM hz
    else 0

theorem resolventLM_apply_apply {z : R} (hz : z ∈ resolventSet f) : resolventLM f z =
    ((z • LinearMap.id) +ᵥ (-f) : E →ₗ.[R] E).inverseLM hz := by
  simp [resolventLM, hz]

/-- The range of the resolvent `R(f, z)` is equal to the domain of `f` for any `z` in the resolvent
set. -/
theorem range_resolventLM (f : E →ₗ.[R] E) {z : R} (hz : z ∈ f.resolventSet) :
    (f.resolventLM z).range = f.domain := by
  simp [resolventLM, hz, inverseLM_range hz]

/-- The first resolvent identity. -/
theorem resolventLM_sub_resolventLM_eq {f : E →ₗ.[R] E} {z₁ z₂ : R} (hz₁ : z₁ ∈ f.resolventSet)
    (hz₂ : z₂ ∈ f.resolventSet) :
    f.resolventLM z₁ - f.resolventLM z₂ = (z₂ - z₁) • f.resolventLM z₁ ∘ₗ f.resolventLM z₂ := by
  rw [resolventLM_apply_apply hz₁, resolventLM_apply_apply hz₂,
    inverseLM_sub_inverseLM_eq hz₁ hz₂ (by simp), ← LinearMap.comp_smul]
  congr 1
  ext x
  rw [LinearMap.smul_apply, compLinearMap_apply (by simp [inverseLM_range hz₂, sub_domain])]
  simp [sub_apply, vadd_apply, vadd_apply, ← sub_smul]

theorem resolventLM_commute [IsCancelMulZero R] [Module.IsTorsionFree R E] {f : E →ₗ.[R] E}
    {z₁ z₂ : R} (hz₁ : z₁ ∈ f.resolventSet) (hz₂ : z₂ ∈ f.resolventSet) :
    f.resolventLM z₁ ∘ₗ f.resolventLM z₂ = f.resolventLM z₂ ∘ₗ f.resolventLM z₁ := by
  by_cases hz : z₁ = z₂
  · rw [hz]
  have h₁ := resolventLM_sub_resolventLM_eq hz₁ hz₂
  have h₂ := resolventLM_sub_resolventLM_eq hz₂ hz₁
  have : (z₁ - z₂) • f.resolventLM z₂ ∘ₗ f.resolventLM z₁ =
      -((z₂ - z₁) • f.resolventLM z₁ ∘ₗ f.resolventLM z₂) := by grind
  rw [← neg_smul, neg_sub] at this
  grind [smul_cancel_of_non_zero_divisor, smul_eq_zero_iff_right]

/-- The second resolvent identity -/
theorem resolventLM_sub_resolventLM_eq' {f g : E →ₗ.[R] E} {z : R} (hz₁ : z ∈ f.resolventSet)
    (hz₂ : z ∈ g.resolventSet) (hfg : g.domain ≤ f.domain) :
    f.resolventLM z - g.resolventLM z =
      f.resolventLM z ∘ₗ ((f - g).compLinearMap (g.resolventLM z)) := by
  rw [resolventLM_apply_apply hz₁, resolventLM_apply_apply hz₂,
    inverseLM_sub_inverseLM_eq hz₁ hz₂ (by simpa)]
  congr 2
  ext x hf hg : 1
  · simpa [sub_domain] using inf_comm g.domain f.domain
  · simpa [sub_apply] using neg_add_eq_sub _ _

end resolvent

end LinearAlgebra

end LinearPMap
