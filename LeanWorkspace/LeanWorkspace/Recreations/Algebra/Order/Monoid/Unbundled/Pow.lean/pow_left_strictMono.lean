import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [Preorder β] [MulLeftStrictMono M] [MulRightStrictMono M] {f : β → M} {n : ℕ}

theorem pow_left_strictMono (hn : n ≠ 0) : StrictMono (· ^ n : M → M) := strictMono_id.pow_const hn

