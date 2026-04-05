import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S] {f : R →+* S} {p : R[X]}

theorem natDegree_map_lt' (hp : f p.leadingCoeff = 0) (hp₀ : 0 < natDegree p) :
    (p.map f).natDegree < p.natDegree := by
  by_cases H : map f p = 0
  · rwa [H, natDegree_zero]
  · exact Polynomial.natDegree_map_lt hp H

