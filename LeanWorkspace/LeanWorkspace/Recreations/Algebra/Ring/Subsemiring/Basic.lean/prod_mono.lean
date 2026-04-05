import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem prod_mono ⦃s₁ s₂ : Subsemiring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ := Set.prod_mono hs ht

