import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

theorem mono_δ (h₀ : IsZero S.L₀.X₂) : Mono S.δ := (S.L₁'.exact_iff_mono (IsZero.eq_zero_of_src h₀ S.L₁'.f)).1 S.L₁'_exact

