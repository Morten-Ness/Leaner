import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

theorem epi_δ (h₃ : IsZero S.L₃.X₂) : Epi S.δ := (S.L₂'.exact_iff_epi (IsZero.eq_zero_of_tgt h₃ S.L₂'.g)).1 S.L₂'_exact

