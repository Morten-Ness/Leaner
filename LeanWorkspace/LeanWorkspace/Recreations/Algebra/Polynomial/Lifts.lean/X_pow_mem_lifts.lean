import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem X_pow_mem_lifts (f : R →+* S) (n : ℕ) : (Polynomial.X ^ n : S[X]) ∈ Polynomial.lifts f := ⟨Polynomial.X ^ n, by
    simp only [coe_mapRingHom, map_pow, map_X]⟩

