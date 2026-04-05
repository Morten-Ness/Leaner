import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

theorem snd_δ : (pullback.snd _ _ : S.P ⟶ _) ≫ S.δ = S.φ₁ ≫ S.v₂₃.τ₁ := S.L₀'_exact.g_desc _ _

