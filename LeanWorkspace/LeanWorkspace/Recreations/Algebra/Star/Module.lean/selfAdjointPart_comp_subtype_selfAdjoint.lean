import Mathlib

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

variable {A} [Invertible (2 : R)]

theorem selfAdjointPart_comp_subtype_selfAdjoint :
    (selfAdjointPart R).comp (selfAdjoint.submodule R A).subtype = .id := LinearMap.ext fun x ↦ x.2.selfAdjointPart_apply R

