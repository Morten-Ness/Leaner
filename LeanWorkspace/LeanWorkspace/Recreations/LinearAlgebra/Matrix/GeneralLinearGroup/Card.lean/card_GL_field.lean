import Mathlib

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]

variable (n : ℕ)

theorem card_GL_field :
    Nat.card (GL (Fin n) 𝔽) = ∏ i : (Fin n), (q ^ n - q ^ (i : ℕ)) := by
  rw [Nat.card_congr (Matrix.equiv_GL_linearindependent n), card_linearIndependent,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, le_refl]

