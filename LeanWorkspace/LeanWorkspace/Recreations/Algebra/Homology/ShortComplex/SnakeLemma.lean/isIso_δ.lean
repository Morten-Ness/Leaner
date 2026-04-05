import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

theorem isIso_δ (h₀ : IsZero S.L₀.X₂) (h₃ : IsZero S.L₃.X₂) : IsIso S.δ := @Balanced.isIso_of_mono_of_epi _ _ _ _ _ S.δ (S.mono_δ h₀) (S.epi_δ h₃)

