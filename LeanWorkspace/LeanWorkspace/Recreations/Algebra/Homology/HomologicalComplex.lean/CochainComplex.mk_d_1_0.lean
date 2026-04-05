import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂) (s : d₀ ≫ d₁ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₄ : V) (d₂ : S.X₃ ⟶ X₄), S.g ≫ d₂ = 0)

theorem mk_d_1_0 : (CochainComplex.mk X₀ X₁ X₂ d₀ d₁ s succ).d 0 1 = d₀ := by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl, Category.comp_id]

