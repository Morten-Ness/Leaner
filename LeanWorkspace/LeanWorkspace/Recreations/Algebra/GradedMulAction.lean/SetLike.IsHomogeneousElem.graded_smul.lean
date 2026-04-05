import Mathlib

variable {ιA ιB ιM : Type*}

variable {S R N M : Type*} [SetLike S R] [SetLike N M]

theorem SetLike.IsHomogeneousElem.graded_smul [VAdd ιA ιB] [SMul R M] {A : ιA → S} {B : ιB → N}
    [SetLike.GradedSMul A B] {a : R} {b : M} :
    SetLike.IsHomogeneousElem A a → SetLike.IsHomogeneousElem B b →
    SetLike.IsHomogeneousElem B (a • b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i +ᵥ j, SetLike.GradedSMul.smul_mem hi hj⟩
