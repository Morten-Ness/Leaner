import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_lt_natDegree_iff (hp : p ≠ 0) : natDegree p < natDegree q ↔ degree p < degree q := ⟨Polynomial.degree_lt_degree, fun h ↦ by
    have hq : q ≠ 0 := Polynomial.ne_zero_of_degree_gt h
    rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at h⟩

