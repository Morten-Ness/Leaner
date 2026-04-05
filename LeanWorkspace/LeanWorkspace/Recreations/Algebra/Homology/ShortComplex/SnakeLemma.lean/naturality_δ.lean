import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

variable (S₁ S₂ S₃ : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem naturality_δ (f : S₁ ⟶ S₂) : S₁.δ ≫ f.f₃.τ₁ = f.f₀.τ₃ ≫ S₂.δ := by
  rw [← cancel_epi (pullback.snd _ _ : S₁.P ⟶ _), S₁.snd_δ_assoc, ← comp_τ₁, ← f.comm₂₃,
    comp_τ₁, naturality_φ₁_assoc, ← S₂.snd_δ, functorP_map, pullback.lift_snd_assoc, assoc]

