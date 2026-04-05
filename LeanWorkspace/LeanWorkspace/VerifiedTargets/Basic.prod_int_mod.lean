import Mathlib

variable {ι α β M N P G : Type*}

theorem prod_int_mod (l : List ℤ) (n : ℤ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l <;> simp [Int.mul_emod, *]

