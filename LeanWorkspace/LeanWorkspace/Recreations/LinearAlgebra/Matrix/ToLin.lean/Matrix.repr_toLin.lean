import Mathlib

variable {R : Type*} [CommSemiring R]

variable {l m n : Type*} [Fintype n] [Finite m] [DecidableEq n]

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

theorem Matrix.repr_toLin (M : Matrix m n R) (x : M₁) :
    v₂.repr (M.toLin v₁ v₂ x) = M.mulVec (v₁.repr x) := by
  rw [← toMatrix_mulVec_repr v₁, toMatrix_toLin]

