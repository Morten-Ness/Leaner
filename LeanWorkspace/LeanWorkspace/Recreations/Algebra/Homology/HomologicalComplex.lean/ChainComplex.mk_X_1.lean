import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁) (s : d₁ ≫ d₀ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₃ : V) (d₂ : X₃ ⟶ S.X₁), d₂ ≫ S.f = 0)

theorem mk_X_1 : (ChainComplex.mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁ := rfl

