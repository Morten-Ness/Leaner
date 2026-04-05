import Mathlib

open scoped Pointwise RightActions

variable {α β : Type*} [DecidableEq β]

variable [GroupWithZero α]

variable [DecidableEq α] {s : Finset α}

theorem inv_op_smul_finset_distrib₀ (a : α) (s : Finset α) : (s <• a)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, MulOpposite.op_eq_zero_iff, not_false_eq_true, ←
      Finset.inv_smul_mem_iff₀, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_inv, MulOpposite.unop_op,
      inv_eq_zero, inv_inv, smul_eq_mul, mul_inv_rev, ha]

