import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem prod_lt_one_iff_of_le_one {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] (hf : ∀ x ∈ s, f x ≤ 1) :
    ∏ x ∈ s, f x < 1 ↔ ∃ x ∈ s, f x < 1 := Finset.one_lt_prod_iff_of_one_le (N := Nᵒᵈ) hf

