import Mathlib

variable {n R : Type*} [Ring R] [LinearOrder R]

variable {A : Matrix n n R}

theorem isIrreducible_transpose_iff :
    Aᵀ.IsIrreducible ↔ A.IsIrreducible := by
  by_cases hA_nonneg : ∀ i j, 0 ≤ A i j
  · exact ⟨fun h ↦
    let hA_T_nonneg : ∀ i j, 0 ≤ (Aᵀ) i j := fun i j => by
      simpa [Matrix.transpose_apply] using hA_nonneg j i
    Matrix.IsIrreducible.transpose h,
   fun h ↦ Matrix.IsIrreducible.transpose h⟩
  · have : ¬ Aᵀ.IsIrreducible := by
      rw [isIrreducible_iff]
      simp only [transpose_apply, isSStronglyConnected_iff, not_and, not_forall, not_exists,
        not_lt, nonpos_iff_eq_zero]
      intro a; simp_all only [implies_true, not_true_eq_false]
    have : ¬ A.IsIrreducible := by
      rw [isIrreducible_iff]; simp_all only [not_forall, not_le, isSStronglyConnected_iff,
      not_and, not_exists, not_lt, nonpos_iff_eq_zero, isEmpty_Prop, IsEmpty.forall_iff]
    simp_all only [not_forall, not_le]

