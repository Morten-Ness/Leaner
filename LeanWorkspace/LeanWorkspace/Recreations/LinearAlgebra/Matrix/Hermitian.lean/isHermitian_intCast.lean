import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Ring α] [StarRing α]

theorem isHermitian_intCast [DecidableEq n] (d : ℤ) : (d : Matrix n n α).IsHermitian := conjTranspose_intCast _

