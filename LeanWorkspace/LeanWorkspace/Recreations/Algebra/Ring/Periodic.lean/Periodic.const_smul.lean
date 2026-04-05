import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.const_smul [AddMonoid α] [Group γ] [DistribMulAction γ α]
    (h : Function.Periodic f c) (a : γ) : Function.Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

