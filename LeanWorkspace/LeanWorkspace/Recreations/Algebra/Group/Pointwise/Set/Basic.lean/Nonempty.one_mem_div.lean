import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s := let ⟨a, ha⟩ := h
  Set.mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

