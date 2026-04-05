import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [AddGroup α] [StarAddMonoid α]

theorem IsHermitian.neg {A : Matrix n n α} (h : A.IsHermitian) : (-A).IsHermitian := IsSelfAdjoint.neg h

