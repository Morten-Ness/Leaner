import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [IdemSemiring α] {a b c : α}

theorem nsmul_eq_self : ∀ {n : ℕ} (_ : n ≠ 0) (a : α), n • a = a
  | 0, h => (h rfl).elim
  | 1, _ => one_nsmul
  | n + 2, _ => fun a ↦ by rw [succ_nsmul, nsmul_eq_self n.succ_ne_zero, add_idem]
