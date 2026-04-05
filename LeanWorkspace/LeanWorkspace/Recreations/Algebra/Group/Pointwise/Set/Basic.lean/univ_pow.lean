import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem univ_pow : ∀ {n : ℕ}, n ≠ 0 → (univ : Set α) ^ n = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => pow_one _
  | n + 2 => fun _ => by rw [pow_succ, univ_pow n.succ_ne_zero, Set.univ_mul_univ]
