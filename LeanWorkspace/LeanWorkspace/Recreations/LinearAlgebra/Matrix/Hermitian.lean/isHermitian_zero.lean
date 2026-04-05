import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [AddMonoid α] [StarAddMonoid α]

theorem isHermitian_zero : (0 : Matrix n n α).IsHermitian := IsSelfAdjoint.zero _

