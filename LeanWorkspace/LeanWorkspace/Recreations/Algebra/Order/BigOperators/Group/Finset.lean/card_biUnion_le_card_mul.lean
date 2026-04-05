import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem card_biUnion_le_card_mul [DecidableEq β] (s : Finset ι) (f : ι → Finset β) (n : ℕ)
    (h : ∀ a ∈ s, #(f a) ≤ n) : #(s.biUnion f) ≤ #s * n := card_biUnion_le.trans <| sum_le_card_nsmul _ _ _ h

