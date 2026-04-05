import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem X_mem_lifts (f : R →+* S) : (Polynomial.X : S[X]) ∈ Polynomial.lifts f := ⟨Polynomial.X, by
    simp only [coe_mapRingHom, map_X]⟩

