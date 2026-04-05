import Mathlib

variable {α : Type*}

variable {α₁ α₂ α₃ : Type*} {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop}
  {rels₂ : FreeMonoid α₂ → FreeMonoid α₂ → Prop} {rels₃ : FreeMonoid α₃ → FreeMonoid α₃ → Prop}

theorem inductionOn₂ {δ : P₁ → P₂ → Prop} (q₁ : P₁) (q₂ : P₂)
    (h : ∀ a b, δ (PresentedMonoid.mk rels₁ a) (PresentedMonoid.mk rels₂ b)) : δ q₁ q₂ := Quotient.inductionOn₂ q₁ q₂ h

