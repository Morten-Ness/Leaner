FAIL
import Mathlib

variable {ι α β M N P G : Type*}

theorem prod_int_mod (l : List ℤ) (n : ℤ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      simp only [List.prod_cons, List.map]
      rw [Int.mul_emod, ih, ← Int.mul_emod, Int.emod_emod]
