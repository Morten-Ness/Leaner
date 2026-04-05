import Mathlib

variable {R A : Type*} [Semiring R]

theorem mul_apply_mul_eq_mul_of_uniqueMul [Mul A] {f g : R[A]} {a0 b0 : A}
    (h : UniqueMul f.support g.support a0 b0) :
    (f * g) (a0 * b0) = f a0 * g b0 := by
  classical
  simp_rw [mul_apply, sum, ← Finset.sum_product']
  refine (Finset.sum_eq_single (a0, b0) ?_ ?_).trans (if_pos rfl) <;> simp_rw [Finset.mem_product]
  · refine fun ab hab hne ↦ if_neg (fun he ↦ hne <| Prod.ext ?_ ?_)
    exacts [(h hab.1 hab.2 he).1, (h hab.1 hab.2 he).2]
  · refine fun hnotMem ↦ ite_eq_right_iff.mpr (fun _ ↦ ?_)
    rcases not_and_or.mp hnotMem with af | bg
    · rw [notMem_support_iff.mp af, zero_mul]
    · rw [notMem_support_iff.mp bg, mul_zero]

