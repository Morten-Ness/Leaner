import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.const_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  by_cases ha : a = 0
  · simp only [ha, zero_smul]
  · simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

