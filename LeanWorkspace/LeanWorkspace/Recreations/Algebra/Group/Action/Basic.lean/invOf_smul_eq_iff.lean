import Mathlib

variable {G M A B α β : Type*}

variable [Monoid α] [MulAction α β] (c : α) (x y : β) [Invertible c]

theorem invOf_smul_eq_iff : ⅟c • x = y ↔ x = c • y := inv_smul_eq_iff (g := unitOfInvertible c)

