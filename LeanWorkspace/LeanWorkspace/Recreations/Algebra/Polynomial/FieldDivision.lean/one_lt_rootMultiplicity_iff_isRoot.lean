import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem one_lt_rootMultiplicity_iff_isRoot
    {p : R[X]} {t : R} (h : p ≠ 0) :
    1 < p.rootMultiplicity t ↔ p.IsRoot t ∧ (derivative p).IsRoot t := by
  rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot_iterate_derivative h]
  refine ⟨fun h ↦ ⟨h 0 (by simp), h 1 (by simp)⟩, fun ⟨h0, h1⟩ m hm ↦ ?_⟩
  obtain (_ | _ | m) := m
  exacts [h0, h1, by lia]

