import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Semiring α] [AddCommMonoid β] [Module α β]

theorem add_smul_subset (a b : α) (s : Set β) : (a + b) • s ⊆ a • s + b • s := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [add_smul] using add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hx)

