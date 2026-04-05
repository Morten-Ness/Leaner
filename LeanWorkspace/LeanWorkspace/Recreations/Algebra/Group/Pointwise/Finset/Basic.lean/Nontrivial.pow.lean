import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [CancelMonoid α] {s : Finset α} {m n : ℕ}

theorem Nontrivial.pow (hs : s.Nontrivial) : ∀ {n}, n ≠ 0 → (s ^ n).Nontrivial
  | 1, _ => by simpa
  | n + 2, _ => by simpa [pow_succ] using (hs.pow n.succ_ne_zero).mul hs
