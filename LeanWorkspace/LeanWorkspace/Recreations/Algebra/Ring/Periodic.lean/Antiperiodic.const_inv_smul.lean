import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.const_inv_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Function.Antiperiodic f c) (a : γ) : Function.Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹

