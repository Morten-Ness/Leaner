import Mathlib

variable {M : Type*}

variable [AddMonoid M]

theorem AddMonoidHom.apply_nat (f : ℕ →+ M) (n : ℕ) : f n = n • f 1 := by
  rw [← multiplesHom_symm_apply, ← multiplesHom_apply, Equiv.apply_symm_apply]

