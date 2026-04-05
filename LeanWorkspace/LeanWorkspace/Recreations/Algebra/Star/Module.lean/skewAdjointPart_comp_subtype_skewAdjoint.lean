import Mathlib

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

variable {A} [Invertible (2 : R)]

theorem skewAdjointPart_comp_subtype_skewAdjoint :
    (skewAdjointPart R).comp (skewAdjoint.submodule R A).subtype = .id := LinearMap.ext fun ⟨x, (hx : _ = _)⟩ ↦ Subtype.ext <| by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, skewAdjointPart_apply_coe, hx,
      sub_neg_eq_add, smul_add, invOf_two_smul_add_invOf_two_smul]; rfl

