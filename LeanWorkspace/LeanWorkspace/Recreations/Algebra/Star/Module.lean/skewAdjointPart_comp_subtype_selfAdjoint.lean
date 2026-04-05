import Mathlib

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

variable {A} [Invertible (2 : R)]

theorem skewAdjointPart_comp_subtype_selfAdjoint :
    (skewAdjointPart R).comp (selfAdjoint.submodule R A).subtype = 0 := LinearMap.ext fun x ↦ x.2.skewAdjointPart_apply R

