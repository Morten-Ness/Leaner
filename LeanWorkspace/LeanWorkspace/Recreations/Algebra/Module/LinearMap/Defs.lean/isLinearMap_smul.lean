import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂]

theorem isLinearMap_smul {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (c : R) :
    IsLinearMap R fun z : M ↦ c • z := by
  refine IsLinearMap.mk (smul_add c) ?_
  intro _ _
  simp only [smul_smul, mul_comm]

