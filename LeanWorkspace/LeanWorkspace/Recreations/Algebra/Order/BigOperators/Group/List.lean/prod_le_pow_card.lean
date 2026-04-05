import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem prod_le_pow_card [Preorder M] [MulRightMono M]
    [MulLeftMono M] (l : List M) (n : M) (h : ∀ x ∈ l, x ≤ n) :
    l.prod ≤ n ^ l.length := by
  simpa only [map_id', map_const', prod_replicate] using List.prod_le_prod' h

