import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] {a p : R[X]}

theorem mem_nonzeroDivisors_of_coeff_mem {p : R[X]} (n : ℕ) (hp : p.coeff n ∈ R⁰) :
    p ∈ R[X]⁰ := Polynomial.mem_nonZeroDivisors_iff.mpr fun r hr ↦ hp.2 _ (by simpa using congr(coeff $hr n))

