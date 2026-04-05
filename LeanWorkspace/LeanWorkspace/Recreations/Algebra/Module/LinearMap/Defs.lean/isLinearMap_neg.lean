import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [AddCommGroup M] [AddCommGroup M₂]

variable [Module R M] [Module R M₂]

theorem isLinearMap_neg : IsLinearMap R fun z : M ↦ -z := IsLinearMap.mk neg_add fun x y ↦ (smul_neg x y).symm

