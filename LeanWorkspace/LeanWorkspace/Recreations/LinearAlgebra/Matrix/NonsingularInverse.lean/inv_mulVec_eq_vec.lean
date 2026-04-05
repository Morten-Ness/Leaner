import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem inv_mulVec_eq_vec {A : Matrix n n α} [Invertible A]
    {u v : n → α} (hM : u = A.mulVec v) : A⁻¹.mulVec u = v := by
  rw [hM, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

