import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem exists_lt_of_prod_lt' [LinearOrder M] [MulRightMono M]
    [MulLeftMono M] {l : List ι} (f g : ι → M)
    (h : (l.map f).prod < (l.map g).prod) : ∃ i ∈ l, f i < g i := by
  contrapose! h
  exact List.prod_le_prod' h

