import Mathlib

open scoped Kronecker

variable [CommSemigroup R]

theorem hadamard_kronecker_hadamard (A B : Matrix l m R) (C D : Matrix n p R) :
    (A ⊙ B) ⊗ₖ (C ⊙ D) = (A ⊗ₖ C) ⊙ (B ⊗ₖ D) := ext fun _ _ => mul_mul_mul_comm _ _ _ _

