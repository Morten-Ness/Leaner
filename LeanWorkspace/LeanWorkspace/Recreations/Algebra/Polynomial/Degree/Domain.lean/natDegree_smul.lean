import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

omit [NoZeroDivisors R] in
theorem natDegree_smul {S : Type*} [Semiring S] [IsDomain S] [Module S R] [Module.IsTorsionFree S R]
    {a : S} (ha : a ≠ 0) : (a • p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp only [hp, smul_zero]
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact (natDegree_smul_le _ _).trans (le_refl _)
    · simp only [coeff_smul]
      apply smul_ne_zero ha
      simp [hp]

