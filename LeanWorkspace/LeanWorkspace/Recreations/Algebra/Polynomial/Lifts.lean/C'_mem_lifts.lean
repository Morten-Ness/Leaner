import Mathlib

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem C'_mem_lifts {f : R →+* S} {s : S} (h : s ∈ Set.range f) : Polynomial.C s ∈ Polynomial.lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use Polynomial.C r
  simp only [coe_mapRingHom, map_C]

