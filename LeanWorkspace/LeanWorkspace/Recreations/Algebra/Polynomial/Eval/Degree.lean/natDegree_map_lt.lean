import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S] {f : R →+* S} {p : R[X]}

theorem natDegree_map_lt (hp : f p.leadingCoeff = 0) (hp₀ : map f p ≠ 0) :
    (p.map f).natDegree < p.natDegree := natDegree_lt_natDegree hp₀ <| Polynomial.degree_map_lt hp <| by rintro rfl; simp at hp₀

