import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem coeff_natDegree_succ_eq_zero {p : R[X]} : p.coeff (p.natDegree + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_add_one _)

-- We need the explicit `Decidable` argument here because an exotic one shows up in a moment!

