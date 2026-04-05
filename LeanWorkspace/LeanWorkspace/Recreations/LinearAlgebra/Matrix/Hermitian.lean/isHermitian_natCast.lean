import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Semiring α] [StarRing α]

theorem isHermitian_natCast [DecidableEq n] (d : ℕ) : (d : Matrix n n α).IsHermitian := conjTranspose_natCast _

