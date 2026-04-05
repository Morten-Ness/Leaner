import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_mul_eq_mk_left (h : MulArchimedeanClass.mk a < MulArchimedeanClass.mk b) : MulArchimedeanClass.mk (a * b) = MulArchimedeanClass.mk a := by
  refine le_antisymm (MulArchimedeanClass.mk_le_mk.mpr ⟨2, ?_⟩) (MulArchimedeanClass.mk_left_le_mk_mul h.le)
  rw [MulArchimedeanClass.mk_lt_mk] at h
  apply (mabs_mul' _ b).trans
  rw [mul_comm b a, pow_two, mul_le_mul_iff_right]
  apply le_of_mul_le_mul_left' (a := |b|ₘ)
  rw [mul_comm a b]
  exact (pow_two |b|ₘ ▸ (h 2).le).trans (mabs_mul' a b)

