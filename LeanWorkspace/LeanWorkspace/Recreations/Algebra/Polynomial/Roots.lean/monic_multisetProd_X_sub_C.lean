import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem monic_multisetProd_X_sub_C (s : Multiset R) : Monic (s.map fun a => X - C a).prod := monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

