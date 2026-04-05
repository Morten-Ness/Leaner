import Mathlib

variable {α β R n m : Type*}

theorem IsDiag.sub [SubtractionMonoid α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag) :
    (A - B).IsDiag := by
  intro i j h
  simp [ha h, hb h]

