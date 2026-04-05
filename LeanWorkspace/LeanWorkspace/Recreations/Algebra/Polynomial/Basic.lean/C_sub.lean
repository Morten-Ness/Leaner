import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

theorem C_sub : Polynomial.C (a - b) = Polynomial.C a - Polynomial.C b := map_sub Polynomial.C a b

