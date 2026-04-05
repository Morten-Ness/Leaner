import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

theorem trinomial_def : Polynomial.trinomial k m n u v w = C u * X ^ k + C v * X ^ m + C w * X ^ n := rfl

