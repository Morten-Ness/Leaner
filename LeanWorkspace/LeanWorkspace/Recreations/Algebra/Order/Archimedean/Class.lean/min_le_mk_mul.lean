import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem min_le_mk_mul (a b : M) : min (MulArchimedeanClass.mk a) (MulArchimedeanClass.mk b) ≤ MulArchimedeanClass.mk (a * b) := by
  by_contra! h
  rw [lt_min_iff] at h
  have h1 := (MulArchimedeanClass.mk_lt_mk.mp h.1 2).trans_le (mabs_mul_le _ _)
  have h2 := (MulArchimedeanClass.mk_lt_mk.mp h.2 2).trans_le (mabs_mul_le _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right, pow_two] at h1 h2
  exact h1.not_gt h2

