import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p : R[X]}

theorem degree_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).degree = p.degree := by
  refine le_antisymm ?_ ?_
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    simp [hm m le_rfl]
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    refine h ?_
    simpa using hm m le_rfl

