import Mathlib

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

variable {A} [Invertible (2 : R)]

theorem IsSelfAdjoint.selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    selfAdjointPart R x = ⟨x, hx⟩ := Subtype.ext (hx.coe_selfAdjointPart_apply R)

