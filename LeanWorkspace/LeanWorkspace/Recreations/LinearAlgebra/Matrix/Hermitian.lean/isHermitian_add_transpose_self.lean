import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [AddCommMonoid α] [StarAddMonoid α]

theorem isHermitian_add_transpose_self (A : Matrix n n α) : (A + Aᴴ).IsHermitian := IsSelfAdjoint.add_star_self A

