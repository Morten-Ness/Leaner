import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [AddCommMonoid α] [StarAddMonoid α]

theorem isHermitian_transpose_add_self (A : Matrix n n α) : (Aᴴ + A).IsHermitian := IsSelfAdjoint.star_add_self A

