import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [CommGroup β] [FunLike F α β] [MonoidHomClass F α β]

theorem smul_graphOn (x : α × β) (s : Set α) (f : F) :
    x • s.graphOn f = (x.1 • s).graphOn fun a ↦ x.2 / f x.1 * f a := by
  ext ⟨a, b⟩
  simp [Set.mem_smul_set_iff_inv_smul_mem, inv_mul_eq_iff_eq_mul, mul_left_comm _ _⁻¹,
    eq_inv_mul_iff_mul_eq, ← mul_div_right_comm, div_eq_iff_eq_mul, mul_comm b]

