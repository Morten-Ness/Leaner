import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁) (s : d₁ ≫ d₀ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₃ : V) (d₂ : X₃ ⟶ S.X₁), d₂ ≫ S.f = 0)

variable (succ' : ∀ {X₀ X₁ : V} (f : X₁ ⟶ X₀), Σ' (X₂ : V) (d : X₂ ⟶ X₁), d ≫ f = 0)

theorem mk'_X_0 : (ChainComplex.mk' X₀ X₁ d₀ succ').X 0 = X₀ := rfl

