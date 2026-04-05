import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

theorem support_map_subset [Semiring R] [Semiring S] (f : R →+* S) (p : R[X]) :
    (map f p).support ⊆ p.support := by
  intro x
  contrapose!
  simp +contextual

