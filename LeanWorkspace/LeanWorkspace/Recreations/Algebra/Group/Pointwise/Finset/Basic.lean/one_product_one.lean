import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem one_product_one [One β] : (1 ×ˢ 1 : Finset (α × β)) = 1 := by ext; simp [Prod.ext_iff]

