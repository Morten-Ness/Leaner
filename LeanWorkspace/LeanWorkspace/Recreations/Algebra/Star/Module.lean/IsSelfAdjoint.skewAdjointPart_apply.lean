import Mathlib

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

variable {A} [Invertible (2 : R)]

theorem IsSelfAdjoint.skewAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    skewAdjointPart R x = 0 := Subtype.ext <| by
  rw [skewAdjointPart_apply_coe, hx.star_eq, sub_self, smul_zero, ZeroMemClass.coe_zero]

