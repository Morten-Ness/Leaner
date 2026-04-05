import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

theorem prod_le_pow_card [MulLeftMono α] (s : Multiset α) (n : α) (h : ∀ x ∈ s, x ≤ n) :
    s.prod ≤ n ^ card s := by
  induction s using Quotient.inductionOn
  simpa using List.prod_le_pow_card _ _ h

