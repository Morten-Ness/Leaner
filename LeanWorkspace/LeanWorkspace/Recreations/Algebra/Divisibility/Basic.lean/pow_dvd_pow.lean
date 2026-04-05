import Mathlib

variable {α : Type*}

variable [Monoid α] {a b c : α} {m n : ℕ}

theorem pow_dvd_pow (a : α) (h : m ≤ n) : a ^ m ∣ a ^ n := ⟨a ^ (n - m), by rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]⟩

