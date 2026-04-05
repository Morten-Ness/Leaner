import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.const_inv_smul [AddMonoid α] [Group γ] [DistribMulAction γ α] (h : Function.Periodic f c)
    (a : γ) : Function.Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹

