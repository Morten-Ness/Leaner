import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_monotoneOn : MonotoneOn MulArchimedeanClass.mk (Set.Iic (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [MulArchimedeanClass.mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_inv_self.mpr ha, mabs_eq_inv_self.mpr hb] at h
  simpa using h

