import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [LinearOrder M] {f g : ι → M} {s t : Finset ι}

variable [IsOrderedCancelMonoid M]

theorem exists_one_lt_of_prod_one_of_exists_ne_one' (f : ι → M) (h₁ : ∏ i ∈ s, f i = 1)
    (h₂ : ∃ i ∈ s, f i ≠ 1) : ∃ i ∈ s, 1 < f i := by
  contrapose! h₁
  obtain ⟨i, m, i_ne⟩ : ∃ i ∈ s, f i ≠ 1 := h₂
  apply ne_of_lt
  calc
    ∏ j ∈ s, f j < ∏ j ∈ s, 1 := Finset.prod_lt_prod' h₁ ⟨i, m, (h₁ i m).lt_of_ne i_ne⟩
    _ = 1 := prod_const_one

