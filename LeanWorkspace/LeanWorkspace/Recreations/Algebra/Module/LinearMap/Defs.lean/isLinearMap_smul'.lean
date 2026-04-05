import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂]

theorem isLinearMap_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (a : M) :
    IsLinearMap R fun c : R ↦ c • a := IsLinearMap.mk (fun x y ↦ add_smul x y a) fun x y ↦ mul_smul x y a

