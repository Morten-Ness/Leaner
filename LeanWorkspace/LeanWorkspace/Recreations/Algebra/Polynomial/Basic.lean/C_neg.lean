import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

theorem C_neg : Polynomial.C (-a) = -Polynomial.C a := map_neg Polynomial.C a

