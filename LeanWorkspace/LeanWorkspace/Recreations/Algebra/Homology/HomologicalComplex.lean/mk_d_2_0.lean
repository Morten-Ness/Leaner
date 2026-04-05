import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂) (s : d₀ ≫ d₁ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₄ : V) (d₂ : S.X₃ ⟶ X₄), S.g ≫ d₂ = 0)

theorem mk_d_2_0 : (CochainComplex.mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 2 = d₁ := by
  change ite (2 = 1 + 1) (d₁ ≫ 𝟙 X₂) 0 = d₁
  rw [if_pos rfl, Category.comp_id]

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.

