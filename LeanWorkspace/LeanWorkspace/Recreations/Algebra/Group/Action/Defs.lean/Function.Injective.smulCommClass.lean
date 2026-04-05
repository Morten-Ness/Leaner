import Mathlib

variable {M N G H α β γ δ : Type*}

theorem Function.Injective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N β] {f : α → β} (hf : Function.Injective f) (h₁ : ∀ (c : M) x, f (c • x) = c • f x)
    (h₂ : ∀ (c : N) x, f (c • x) = c • f x) : SMulCommClass M N α where
  smul_comm c₁ c₂ x := hf <| by simp only [h₁, h₂, smul_comm c₁ c₂ (f x)]

