import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S] {f : R →+* S} {p : R[X]}

theorem map_monic_ne_zero (hp : p.Monic) [Nontrivial S] : p.map f ≠ 0 := fun h =>
  f.map_one_ne_zero ((Polynomial.map_monic_eq_zero_iff hp).mp h _)

