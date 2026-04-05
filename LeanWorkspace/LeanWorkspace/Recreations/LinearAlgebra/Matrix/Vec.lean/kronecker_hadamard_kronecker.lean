import Mathlib

open scoped Kronecker

variable [CommSemigroup R]

theorem kronecker_hadamard_kronecker
    (A : Matrix l m R) (B : Matrix n p R) (C : Matrix l m R) (D : Matrix n p R) :
    (A ⊗ₖ B) ⊙ (C ⊗ₖ D) = (A ⊙ C) ⊗ₖ (B ⊙ D) := Matrix.hadamard_kronecker_hadamard _ _ _ _ |>.symm

