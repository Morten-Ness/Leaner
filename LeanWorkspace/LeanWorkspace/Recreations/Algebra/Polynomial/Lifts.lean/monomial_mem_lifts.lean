import Mathlib

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem monomial_mem_lifts {s : S} (n : ℕ) (h : s ∈ Set.range f) : monomial n s ∈ Polynomial.lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use monomial n r
  simp only [coe_mapRingHom, map_monomial]

