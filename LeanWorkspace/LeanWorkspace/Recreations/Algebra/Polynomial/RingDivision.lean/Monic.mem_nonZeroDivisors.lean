import Mathlib

open scoped nonZeroDivisors Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem Monic.mem_nonZeroDivisors {p : R[X]} (h : p.Monic) : p ∈ R[X]⁰ := mem_nonzeroDivisors_of_coeff_mem _ (h.coeff_natDegree ▸ one_mem R⁰)

