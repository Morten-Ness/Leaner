import Mathlib

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

variable {A} [Invertible (2 : R)]

theorem IsSelfAdjoint.coe_selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    (selfAdjointPart R x : A) = x := by
  rw [selfAdjointPart_apply_coe, hx.star_eq, smul_add, invOf_two_smul_add_invOf_two_smul]

