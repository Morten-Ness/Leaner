import Mathlib

variable {R : Type*}

variable [Ring R]

theorem Splits.comp_neg_X {f : R[X]} (hf : f.Splits) : (f.comp (-X)).Splits := by
  refine Submonoid.closure_induction ?_ (by simp)
    (fun f g _ _ hf hg ↦ mul_comp_neg_X f g ▸ hf.mul hg) hf
  · rintro f (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · simp
    · rw [add_comp, X_comp, C_comp, neg_add_eq_sub, ← neg_sub]
      exact (X_sub_C a).neg

