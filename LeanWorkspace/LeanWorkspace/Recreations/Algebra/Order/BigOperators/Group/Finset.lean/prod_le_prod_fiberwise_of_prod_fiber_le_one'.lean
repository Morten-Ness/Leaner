import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

variable {ι' : Type*} [DecidableEq ι']

theorem prod_le_prod_fiberwise_of_prod_fiber_le_one' [MulLeftMono N] {t : Finset ι'} {g : ι → ι'}
    {f : ι → N} (h : ∀ y ∉ t, ∏ x ∈ s with g x = y, f x ≤ 1) :
    ∏ x ∈ s, f x ≤ ∏ y ∈ t, ∏ x ∈ s with g x = y, f x := Finset.prod_fiberwise_le_prod_of_one_le_prod_fiber' (N := Nᵒᵈ) h

