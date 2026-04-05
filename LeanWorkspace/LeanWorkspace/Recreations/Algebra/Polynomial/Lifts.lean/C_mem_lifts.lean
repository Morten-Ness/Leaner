import Mathlib

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem C_mem_lifts (f : R →+* S) (r : R) : Polynomial.C (f r) ∈ Polynomial.lifts f := ⟨Polynomial.C r, by
    simp only [coe_mapRingHom, map_C]⟩

