import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {M : Type*} {M₂ : Type*}

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂}

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

include τ₁₂ in
theorem ext_on_codisjoint {f g : F} {S T : Submodule R M} (hST : Codisjoint S T)
    (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) : f = g := DFunLike.ext _ _ fun _ ↦ LinearMap.eqOn_sup hS hT <| hST.eq_top.symm ▸ trivial

