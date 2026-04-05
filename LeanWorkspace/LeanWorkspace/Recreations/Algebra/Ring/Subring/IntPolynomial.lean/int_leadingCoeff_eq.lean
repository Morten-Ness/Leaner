import Mathlib

open scoped Polynomial

variable {K : Type*} [Field K] (R : Subring K)

variable (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R)

theorem int_leadingCoeff_eq : ↑(P.int R hP).leadingCoeff = P.leadingCoeff := rfl

