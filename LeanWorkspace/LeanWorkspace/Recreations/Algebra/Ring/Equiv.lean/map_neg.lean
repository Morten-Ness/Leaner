import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] (f : R ≃+* S) (x y : R)

theorem map_neg : f (-x) = -f x := map_neg f x

