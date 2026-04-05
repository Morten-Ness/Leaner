import Mathlib

open scoped Function -- required for scoped `on` notation

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem degree_map_eq_of_injective {f : R →+* S} (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).degree = p.degree := by
  simp [hf, map_ne_zero_iff, ne_or_eq]

