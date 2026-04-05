import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] [CommSemiring S] (f : R →+* S)

theorem IsRoot.map {f : R →+* S} {x : R} {p : R[X]} (h : IsRoot p x) : IsRoot (p.map f) (f x) := by
  rw [IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom, h.eq_zero, f.map_zero]

