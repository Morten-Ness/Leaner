import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

omit [IsDomain R] in
theorem Splits.of_splits_map {S : Type*} [CommRing S] [IsDomain S] [IsSimpleRing R] (i : R →+* S)
    (hf : Polynomial.Splits (f.map i)) (hi : ∀ a ∈ (f.map i).roots, a ∈ i.range) : Polynomial.Splits f := hf.of_splits_map_of_injective i.injective hi

