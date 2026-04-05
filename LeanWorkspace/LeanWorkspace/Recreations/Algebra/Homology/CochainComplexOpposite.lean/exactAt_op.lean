import Mathlib

variable (C : Type*) [Category* C]

variable {C} [Preadditive C]

theorem exactAt_op {K : CochainComplex C ℤ} {n : ℤ} (hK : K.ExactAt n)
    (m : ℤ) (hm : n + m = 0 := by lia) :
    ((CochainComplex.opEquivalence C).functor.obj (op K)).ExactAt m := by
  obtain rfl : n = -m := by lia
  rw [HomologicalComplex.exactAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp),
    ← ShortComplex.exact_unop_iff]
  rwa [HomologicalComplex.exactAt_iff' _ (-(m + 1)) (-m) (-(m - 1)) (by grind [prev])
    (by grind [next])] at hK

