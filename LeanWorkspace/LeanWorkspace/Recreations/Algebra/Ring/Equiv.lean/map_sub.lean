import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] (f : R ≃+* S) (x y : R)

theorem map_sub : f (x - y) = f x - f y := map_sub f x y

