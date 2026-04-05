import Mathlib

variable {ι α M N : Type*}

theorem all_one_of_le_one_le_of_prod_eq_one [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
    {l : List M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) (hl₂ : l.prod = 1) {x : M} (hx : x ∈ l) : x = 1 := _root_.le_antisymm (hl₂ ▸ List.single_le_prod hl₁ _ hx) (hl₁ x hx)

