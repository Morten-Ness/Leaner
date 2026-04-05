import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem val_inv_inj {u₁ u₂ : αˣ} : ((u₁⁻¹ : αˣ) : α) = u₂⁻¹ ↔ (u₁ : α) = u₂ := Units.ext_iff.symm.trans <| inv_inj.trans Units.ext_iff

