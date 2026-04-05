import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [Preorder β] [MulLeftMono M] [MulRightMono M]

theorem pow_left_mono (n : ℕ) : Monotone fun a : M => a ^ n := monotone_id.pow_const _

