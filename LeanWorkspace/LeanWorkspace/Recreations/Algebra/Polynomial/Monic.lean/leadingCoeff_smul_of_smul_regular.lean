import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p : R[X]}

theorem leadingCoeff_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).leadingCoeff = k • p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, coeff_smul,
    Polynomial.natDegree_smul_of_smul_regular p h]

