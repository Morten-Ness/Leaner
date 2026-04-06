import Mathlib

variable {A M G α β γ : Type*}

theorem zpow_apply_comm {α : Type*} (σ : Equiv.Perm α) (m n : ℤ) {x : α} :
    (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) := by
  simp_rw [show ((σ ^ m) ((σ ^ n) x)) = ((σ ^ m) * (σ ^ n)) x by rfl,
    show ((σ ^ n) ((σ ^ m) x)) = ((σ ^ n) * (σ ^ m)) x by rfl]
  rw [← zpow_add, add_comm, zpow_add]
