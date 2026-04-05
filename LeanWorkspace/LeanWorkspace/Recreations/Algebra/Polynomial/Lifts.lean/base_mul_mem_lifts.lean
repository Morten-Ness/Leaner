import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem base_mul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ Polynomial.lifts f) : Polynomial.C (f r) * p ∈ Polynomial.lifts f := by
  simp only [Polynomial.lifts, RingHom.mem_rangeS] at hp ⊢
  obtain ⟨p₁, rfl⟩ := hp
  use Polynomial.C r * p₁
  simp only [coe_mapRingHom, map_C, map_mul]

