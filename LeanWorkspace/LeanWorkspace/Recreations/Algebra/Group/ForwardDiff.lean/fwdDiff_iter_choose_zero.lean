import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem fwdDiff_iter_choose_zero (m n : ℕ) :
    Δ_[1]^[n] (fun x ↦ x.choose m : ℕ → ℤ) 0 = if n = m then 1 else 0 := by
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · rcases Nat.exists_eq_add_of_lt hmn with ⟨k, rfl⟩
    simp_rw [hmn.ne', if_false, (by ring : m + k + 1 = k + 1 + m), iterate_add_apply,
      add_zero m ▸ fwdDiff_iter_choose 0 m, choose_zero_right, iterate_one, cast_one, fwdDiff_const,
      fwdDiff_iter_eq_sum_shift, smul_zero, sum_const_zero]
  · simp only [if_true, add_zero m ▸ fwdDiff_iter_choose 0 m, choose_zero_right, cast_one]
  · rcases Nat.exists_eq_add_of_lt hnm with ⟨k, rfl⟩
    simp_rw [hnm.ne, if_false, add_assoc n k 1, fwdDiff_iter_choose, choose_zero_succ, cast_zero]

