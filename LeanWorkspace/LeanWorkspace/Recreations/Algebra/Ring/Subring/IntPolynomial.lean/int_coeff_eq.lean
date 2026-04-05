import Mathlib

open scoped Polynomial

variable {K : Type*} [Field K] (R : Subring K)

variable (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R)

theorem int_coeff_eq (n : ℕ) : ↑((P.int R hP).coeff n) = P.coeff n := rfl

