import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem monic_finprod_X_sub_C {α : Type*} (b : α → R) : Monic (∏ᶠ k, (X - C (b k))) := monic_finprod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

