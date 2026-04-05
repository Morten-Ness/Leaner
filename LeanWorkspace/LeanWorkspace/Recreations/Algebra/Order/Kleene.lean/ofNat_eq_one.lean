import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [IdemSemiring α] {a b c : α}

theorem ofNat_eq_one {n : ℕ} [n.AtLeastTwo] : (ofNat(n) : α) = 1 := natCast_eq_one <| Nat.ne_zero_of_lt Nat.AtLeastTwo.prop

