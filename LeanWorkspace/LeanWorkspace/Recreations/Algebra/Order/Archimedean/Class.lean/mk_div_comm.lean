import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_div_comm (a b : M) : MulArchimedeanClass.mk (a / b) = MulArchimedeanClass.mk (b / a) := by
  rw [← MulArchimedeanClass.mk_inv, inv_div]

