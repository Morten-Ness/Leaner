import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

theorem submatrix_hadamard {l o : Type*} [Mul α]
    (A B : Matrix m n α) (e : l → m) (f : o → n) :
    (A ⊙ B).submatrix e f = A.submatrix e f ⊙ B.submatrix e f := rfl

