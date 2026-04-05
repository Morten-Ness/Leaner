import Mathlib

variable {α : Type*}

variable {α₁ α₂ α₃ : Type*} {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop}
  {rels₂ : FreeMonoid α₂ → FreeMonoid α₂ → Prop} {rels₃ : FreeMonoid α₃ → FreeMonoid α₃ → Prop}

theorem inductionOn {δ : P₁ → Prop} (q : P₁) (h : ∀ a, δ (PresentedMonoid.mk rels₁ a)) : δ q := Quotient.ind h q

