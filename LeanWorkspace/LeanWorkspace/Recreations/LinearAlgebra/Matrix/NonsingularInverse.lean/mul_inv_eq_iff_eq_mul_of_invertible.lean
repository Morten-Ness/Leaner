import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem mul_inv_eq_iff_eq_mul_of_invertible (A : Matrix n n α) [Invertible A] (B C : Matrix m n α) :
    B * A⁻¹ = C ↔ B = C * A := ⟨fun h => by rw [← h, Matrix.inv_mul_cancel_right_of_invertible],
   fun h => by rw [h, Matrix.mul_inv_cancel_right_of_invertible]⟩

