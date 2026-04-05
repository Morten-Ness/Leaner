import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l : List ι} {f g : ι → M} (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).prod ≤ (l.map g).prod := List.Forall₂.prod_le_prod' <| by simpa

