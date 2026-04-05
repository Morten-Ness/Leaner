import Mathlib

open scoped nonZeroDivisors Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem mem_nonZeroDivisors_of_trailingCoeff {p : R[X]} (h : p.trailingCoeff ∈ R⁰) : p ∈ R[X]⁰ := mem_nonzeroDivisors_of_coeff_mem _ h

