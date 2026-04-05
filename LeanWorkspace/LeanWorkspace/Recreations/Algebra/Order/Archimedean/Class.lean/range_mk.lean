import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem range_mk : Set.range (MulArchimedeanClass.mk (M := M)) = Set.univ := Set.range_eq_univ.mpr (MulArchimedeanClass.mk_surjective M)

