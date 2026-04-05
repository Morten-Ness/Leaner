import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p : R[X]}

theorem natDegree_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [← Nat.cast_inj (R := WithBot ℕ), ← degree_eq_natDegree hp, ← degree_eq_natDegree,
    Polynomial.degree_smul_of_smul_regular p h]
  contrapose! hp
  rw [← smul_zero k] at hp
  exact h.polynomial hp

