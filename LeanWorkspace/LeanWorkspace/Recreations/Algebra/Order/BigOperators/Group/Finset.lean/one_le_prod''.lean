import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem one_le_prod'' [MulLeftMono N] (h : ∀ i : ι, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := Finset.one_le_prod' fun i _ ↦ h i

