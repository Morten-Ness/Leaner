import Mathlib

variable {ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]

variable [Finite ι] [Infinite K]

theorem Module.exists_dual_forall_apply_ne_zero (v : ι → M) (hv : ∀ i, v i ≠ 0) :
    ∃ f : Dual K M, ∀ i, f (v i) ≠ 0 := by
  refine Dual.exists_forall_ne_zero_of_forall_exists (fun i ↦ Dual.eval K M (v i)) fun i ↦ ?_
  by_contra! contra
  simp_rw [Dual.eval_apply, forall_dual_apply_eq_zero_iff] at contra
  exact hv i contra

