import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂) (s : d₀ ≫ d₁ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₄ : V) (d₂ : S.X₃ ⟶ X₄), S.g ≫ d₂ = 0)

variable (succ' : ∀ {X₀ X₁ : V} (f : X₀ ⟶ X₁), Σ' (X₂ : V) (d : X₁ ⟶ X₂), f ≫ d = 0)

theorem mk'_X_1 : (CochainComplex.mk' X₀ X₁ d₀ succ').X 1 = X₁ := rfl

