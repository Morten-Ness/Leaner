import Mathlib

variable {α β R n m : Type*}

theorem IsDiag.neg [SubtractionMonoid α] {A : Matrix n n α} (ha : A.IsDiag) : (-A).IsDiag := by
  intro i j h
  simp [ha h]

