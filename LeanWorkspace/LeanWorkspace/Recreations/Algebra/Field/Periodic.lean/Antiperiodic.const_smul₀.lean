import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.const_smul₀ [AddMonoid α] [Neg β] [GroupWithZero γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a ≠ 0) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

