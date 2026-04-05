import Mathlib

variable {A M G α β γ : Type*}

theorem zpow_apply_comm {α : Type*} (σ : Equiv.Perm α) (m n : ℤ) {x : α} :
    (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) := by
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, zpow_mul_comm]

