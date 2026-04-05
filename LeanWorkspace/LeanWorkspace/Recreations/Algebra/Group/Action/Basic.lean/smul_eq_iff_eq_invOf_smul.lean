import Mathlib

variable {G M A B α β : Type*}

variable [Monoid α] [MulAction α β] (c : α) (x y : β) [Invertible c]

theorem smul_eq_iff_eq_invOf_smul : c • x = y ↔ x = ⅟c • y := smul_eq_iff_eq_inv_smul (g := unitOfInvertible c)

