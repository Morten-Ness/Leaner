import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [NonAssocSemiring α] [StarRing α]

theorem isHermitian_one [DecidableEq n] : (1 : Matrix n n α).IsHermitian := conjTranspose_one

