import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem one_mem_inv_mul_iff : (1 : α) ∈ t⁻¹ * s ↔ ¬Disjoint s t := by
  aesop (add simp [not_disjoint_iff_nonempty_inter, Set.mem_mul, mul_eq_one_iff_eq_inv, Set.Nonempty])

