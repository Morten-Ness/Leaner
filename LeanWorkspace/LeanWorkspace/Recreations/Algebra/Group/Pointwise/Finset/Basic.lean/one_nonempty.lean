import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem one_nonempty : (1 : Finset α).Nonempty := ⟨1, Finset.one_mem_one⟩

