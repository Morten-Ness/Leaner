import Mathlib

variable {F α β γ : Type*}

variable [CancelMonoid α] {s t : Set α} {a : α} {n : ℕ}

theorem Nontrivial.pow (hs : s.Nontrivial) : ∀ {n}, n ≠ 0 → (s ^ n).Nontrivial
  | 1, _ => by simpa
  | n + 2, _ => by simpa [pow_succ] using (hs.pow n.succ_ne_zero).mul hs
