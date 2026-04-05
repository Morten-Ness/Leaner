import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem prod_le_pow_card [MulLeftMono N] (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, f x ≤ n) :
    s.prod f ≤ n ^ #s := by
  refine (Multiset.prod_le_pow_card (s.val.map f) n ?_).trans ?_
  · simpa using h
  · simp

