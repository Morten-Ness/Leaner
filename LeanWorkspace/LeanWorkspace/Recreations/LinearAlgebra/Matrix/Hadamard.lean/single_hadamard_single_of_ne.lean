import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq m] [DecidableEq n] [MulZeroClass α]

theorem single_hadamard_single_of_ne
    {ia : m} {ja : n} {ib : m} {jb : n} (h : ¬(ia = ib ∧ ja = jb)) (a b : α) :
    single ia ja a ⊙ single ib jb b = 0 := by
  rw [not_and_or] at h
  cases h <;> (simp only [single]; aesop)

