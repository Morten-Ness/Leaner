import Mathlib

variable {M N : Type*}

theorem not_irreducible_of_not_unit_dvdNotUnit [CommMonoidWithZero M] {p q : M} (hp : ¬IsUnit p)
    (h : DvdNotUnit p q) : ¬Irreducible q := mt h.isUnit_of_irreducible_right hp

