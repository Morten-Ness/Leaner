import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem prod_mono ⦃s₁ s₂ : Subring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subring S⦄ (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ := Set.prod_mono hs ht

