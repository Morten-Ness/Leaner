import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem inv_mul_eq_iff_eq_mul_of_invertible (A : Matrix n n α) [Invertible A] (B C : Matrix n m α) :
    A⁻¹ * B = C ↔ B = A * C := ⟨fun h => by rw [← h, Matrix.mul_inv_cancel_left_of_invertible],
   fun h => by rw [h, Matrix.inv_mul_cancel_left_of_invertible]⟩

