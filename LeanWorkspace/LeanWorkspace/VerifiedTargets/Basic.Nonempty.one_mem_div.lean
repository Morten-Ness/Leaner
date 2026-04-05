import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s := let ⟨a, ha⟩ := h
  Finset.mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

