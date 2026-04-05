import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem min_le_mk_of_le_of_le {x y z : M} (hy : y ≤ x) (hz : x ≤ z) : min (MulArchimedeanClass.mk y) (MulArchimedeanClass.mk z) ≤ MulArchimedeanClass.mk x := by
  have H := mabs_le_max_mabs_mabs hy hz
  rw [← mabs_of_one_le (le_max_of_le_left (one_le_mabs y))] at H
  apply (MulArchimedeanClass.mk_le_mk_of_mabs H).trans'
  obtain h | h := le_total |y|ₘ |z|ₘ
  · rw [max_eq_right h, min_eq_right, MulArchimedeanClass.mk_mabs]
    exact MulArchimedeanClass.mk_le_mk_of_mabs h
  · rw [max_eq_left h, min_eq_left, MulArchimedeanClass.mk_mabs]
    exact MulArchimedeanClass.mk_le_mk_of_mabs h

