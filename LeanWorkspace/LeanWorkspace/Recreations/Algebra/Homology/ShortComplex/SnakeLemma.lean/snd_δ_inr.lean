import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem snd_δ_inr : (pullback.snd _ _ : S.P ⟶ _) ≫ S.δ ≫ (pushout.inr _ _ : _ ⟶ S.P') =
    pullback.fst _ _ ≫ S.v₁₂.τ₂ ≫ pushout.inl _ _ := by
  simp only [snd_δ_assoc, ← pushout.condition, CategoryTheory.ShortComplex.SnakeInput.φ₂, φ₁_L₂_f_assoc, assoc]

