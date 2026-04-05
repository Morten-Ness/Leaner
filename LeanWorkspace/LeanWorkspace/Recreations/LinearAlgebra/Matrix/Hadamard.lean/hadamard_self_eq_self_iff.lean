import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

theorem hadamard_self_eq_self_iff [Mul α] {A : Matrix m n α} :
    A ⊙ A = A ↔ ∀ i j, IsIdempotentElem (A i j) := ext_iff.symm

