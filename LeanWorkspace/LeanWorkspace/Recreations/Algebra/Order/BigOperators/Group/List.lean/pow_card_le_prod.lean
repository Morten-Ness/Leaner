import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem pow_card_le_prod [Preorder M] [MulRightMono M]
    [MulLeftMono M] (l : List M) (n : M) (h : ∀ x ∈ l, n ≤ x) :
    n ^ l.length ≤ l.prod := @List.prod_le_pow_card Mᵒᵈ _ _ _ _ l n h

