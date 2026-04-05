import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

variable {F : Type*} [Field F] (P : RingPreordering F)

theorem eq_zero_of_mem_of_neg_mem {x} (h : x ∈ P) (h2 : -x ∈ P) : x = 0 := by
  by_contra
  have mem : -x * x⁻¹ ∈ P := by aesop (erase simp neg_mul)
  field_simp at mem
  exact RingPreordering.neg_one_notMem P mem

