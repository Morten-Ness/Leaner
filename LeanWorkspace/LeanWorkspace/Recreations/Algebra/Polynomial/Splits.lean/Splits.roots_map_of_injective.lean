import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.roots_map_of_injective {S : Type*} [CommRing S] [IsDomain S]
    (hf : f.Splits) {i : R →+* S} (hi : Function.Injective i) : (f.map i).roots = f.roots.map i := (roots_map_of_injective_of_card_eq_natDegree hi hf.natDegree_eq_card_roots.symm).symm

