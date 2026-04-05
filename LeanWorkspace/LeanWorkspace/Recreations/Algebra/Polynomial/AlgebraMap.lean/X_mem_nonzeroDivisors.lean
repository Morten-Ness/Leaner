import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] {a p : R[X]}

theorem X_mem_nonzeroDivisors : Polynomial.X ∈ R[X]⁰ := Polynomial.mem_nonzeroDivisors_of_coeff_mem 1 (by simp [one_mem])

