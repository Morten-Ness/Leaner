import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem prod_mono {s₁ s₂ : Subsemigroup M} {t₁ t₂ : Subsemigroup N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ := Set.prod_mono hs ht

