import Mathlib

theorem Int.associated_natAbs (k : ℤ) : Associated k k.natAbs := associated_of_dvd_dvd (Int.dvd_natCast.mpr dvd_rfl) (Int.natAbs_dvd.mpr dvd_rfl)

