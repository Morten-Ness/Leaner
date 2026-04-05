import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem monic_prod_X_sub_C {α : Type*} (b : α → R) (s : Finset α) :
    Monic (∏ a ∈ s, (X - C (b a))) := monic_prod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

