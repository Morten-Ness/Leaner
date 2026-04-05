import Mathlib

variable {ι : Type*}

variable {R S : Type*} [SetLike S R]

theorem SetLike.IsHomogeneousElem.mul [Add ι] [Mul R] {A : ι → S} [SetLike.GradedMul A] {a b : R} :
    SetLike.IsHomogeneousElem A a → SetLike.IsHomogeneousElem A b →
    SetLike.IsHomogeneousElem A (a * b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.mul_mem_graded hi hj⟩
