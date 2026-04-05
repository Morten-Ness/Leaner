import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.roots_map {S : Type*} [CommRing S] [IsDomain S] [IsSimpleRing R]
    (hf : f.Splits) (i : R →+* S) : (f.map i).roots = f.roots.map i := hf.roots_map_of_injective i.injective

