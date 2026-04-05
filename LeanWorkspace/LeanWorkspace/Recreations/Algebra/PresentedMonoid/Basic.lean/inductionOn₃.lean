import Mathlib

variable {α : Type*}

variable {α₁ α₂ α₃ : Type*} {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop}
  {rels₂ : FreeMonoid α₂ → FreeMonoid α₂ → Prop} {rels₃ : FreeMonoid α₃ → FreeMonoid α₃ → Prop}

theorem inductionOn₃ {δ : P₁ → P₂ → P₃ → Prop} (q₁ : P₁)
    (q₂ : P₂) (q₃ : P₃) (h : ∀ a b c, δ (PresentedMonoid.mk rels₁ a) (PresentedMonoid.mk rels₂ b) (PresentedMonoid.mk rels₃ c)) :
    δ q₁ q₂ q₃ := Quotient.inductionOn₃ q₁ q₂ q₃ h

