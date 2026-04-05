import Mathlib

variable {α β R n m : Type*}

theorem IsDiag.smul [Zero α] [SMulZeroClass R α] (k : R) {A : Matrix n n α}
    (ha : A.IsDiag) : (k • A).IsDiag := by
  intro i j h
  simp [ha h]

