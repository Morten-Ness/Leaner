import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem L₀X₂ToP_comp_pullback_snd : S.L₀X₂ToP ≫ pullback.snd _ _ = S.L₀.g := by simp

