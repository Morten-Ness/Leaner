import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem prod_eq_one_iff_of_le_one' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] :
    (∀ i ∈ s, f i ≤ 1) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) := Finset.prod_eq_one_iff_of_one_le' (N := Nᵒᵈ)

