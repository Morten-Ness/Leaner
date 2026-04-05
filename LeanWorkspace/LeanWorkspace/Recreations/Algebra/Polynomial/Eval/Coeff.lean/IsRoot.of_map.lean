import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] [CommSemiring S] (f : R →+* S)

theorem IsRoot.of_map {R} [Ring R] {f : R →+* S} {x : R} {p : R[X]} (h : IsRoot (p.map f) (f x))
    (hf : Function.Injective f) : IsRoot p x := by
  rwa [IsRoot, ← (injective_iff_map_eq_zero' f).mp hf, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]

