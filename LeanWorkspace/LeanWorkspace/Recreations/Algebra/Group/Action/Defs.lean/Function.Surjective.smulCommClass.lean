import Mathlib

variable {M N G H α β γ δ : Type*}

theorem Function.Surjective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N α] {f : α → β} (hf : Function.Surjective f) (h₁ : ∀ (c : M) x, f (c • x) = c • f x)
    (h₂ : ∀ (c : N) x, f (c • x) = c • f x) : SMulCommClass M N β where
  smul_comm c₁ c₂ := hf.forall.2 fun x ↦ by simp only [← h₁, ← h₂, smul_comm c₁ c₂ x]

