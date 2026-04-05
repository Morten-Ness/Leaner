import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem dvdNotUnit_iff_lt {a b : Associates M} : DvdNotUnit a b ↔ a < b := Associated.symm dvd_and_not_dvd_iff

