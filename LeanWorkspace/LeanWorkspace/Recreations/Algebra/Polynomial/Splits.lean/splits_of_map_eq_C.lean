import Mathlib

open scoped Polynomial

variable {R : Type*}

variable {F : Type u} {K : Type v} {L : Type w}

variable [CommRing K] [Field L] [Field F]

variable (i : K →+* L)

theorem splits_of_map_eq_C {f : K[X]} {a : L} (h : f.map i = Polynomial.C a) : Polynomial.Splits (f.map i) := h ▸ Polynomial.Splits.C a

