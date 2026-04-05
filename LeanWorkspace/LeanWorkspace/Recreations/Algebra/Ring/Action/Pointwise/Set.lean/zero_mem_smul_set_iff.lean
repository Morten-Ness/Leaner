import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Semiring α] [AddCommMonoid β] [Module α β]

variable [IsDomain α] [Module.IsTorsionFree α β] {a : α} {s : Set α} {t : Set β}

theorem zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
  refine ⟨?_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(smul_eq_zero.1 h).resolve_left ha] at hb

