import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.const_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Function.Antiperiodic f c) (a : γ) : Function.Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

