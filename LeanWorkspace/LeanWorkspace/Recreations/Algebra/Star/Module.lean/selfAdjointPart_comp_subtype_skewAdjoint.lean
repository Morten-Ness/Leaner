import Mathlib

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

variable {A} [Invertible (2 : R)]

theorem selfAdjointPart_comp_subtype_skewAdjoint :
    (selfAdjointPart R).comp (skewAdjoint.submodule R A).subtype = 0 := LinearMap.ext fun ⟨x, (hx : _ = _)⟩ ↦ Subtype.ext <| by simp [hx]

