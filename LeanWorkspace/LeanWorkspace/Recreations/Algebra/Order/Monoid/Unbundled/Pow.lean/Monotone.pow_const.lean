import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [Preorder β] [MulLeftMono M] [MulRightMono M]

theorem Monotone.pow_const {f : β → M} (hf : Monotone f) : ∀ n : ℕ, Monotone fun a => f a ^ n
  | 0 => by simpa using monotone_const
  | n + 1 => by
    simp_rw [pow_succ]
    exact (Monotone.pow_const hf _).mul' hf
