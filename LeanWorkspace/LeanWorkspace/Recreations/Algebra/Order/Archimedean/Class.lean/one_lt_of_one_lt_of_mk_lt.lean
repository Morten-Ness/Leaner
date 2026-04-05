import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem one_lt_of_one_lt_of_mk_lt (ha : 1 < a) (hab : MulArchimedeanClass.mk a < MulArchimedeanClass.mk (b / a)) :
    1 < b := by
  suffices a⁻¹ < b / a by
    simpa using this
  apply MulArchimedeanClass.lt_of_mk_lt_mk_of_le_one
  · simpa using hab
  · simpa using ha.le

