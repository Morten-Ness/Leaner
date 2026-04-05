import Mathlib

variable {F α β γ : Type*}

variable [One α] {s : Set α} {a : α}

theorem one_prod_one [One β] : (1 ×ˢ 1 : Set (α × β)) = 1 := by ext; simp [Prod.ext_iff]

