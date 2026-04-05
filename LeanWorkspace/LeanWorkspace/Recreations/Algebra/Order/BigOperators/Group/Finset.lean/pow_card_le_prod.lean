import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem pow_card_le_prod [MulLeftMono N] (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, n ≤ f x) :
    n ^ #s ≤ s.prod f := Finset.prod_le_pow_card (N := Nᵒᵈ) _ _ _ h

