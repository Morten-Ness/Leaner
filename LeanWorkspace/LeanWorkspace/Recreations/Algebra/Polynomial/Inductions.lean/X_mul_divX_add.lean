import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_mul_divX_add (p : R[X]) : Polynomial.X * Polynomial.divX p + Polynomial.C (p.coeff 0) = p := ext <| by rintro ⟨_ | _⟩ <;> simp [coeff_C]

