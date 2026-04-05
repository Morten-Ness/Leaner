import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem exists_le_of_prod_le' [LinearOrder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (h : (l.map f).prod ≤ (l.map g).prod) : ∃ x ∈ l, f x ≤ g x := by
  contrapose! h
  exact List.prod_lt_prod_of_ne_nil hl _ _ h

