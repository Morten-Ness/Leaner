import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem closure_induction_left
    {s : Set M} {motive : (m : M) → m ∈ closure s → Prop} (one : motive 1 (one_mem _))
    (mul_left : ∀ x (hx : x ∈ s), ∀ y hy,
      motive y hy → motive (x * y) (mul_mem (subset_closure hx) hy))
    {x : M} (h : x ∈ closure s) : motive x h := by
  simp_rw [Submonoid.closure_eq_mrange] at h
  obtain ⟨l, rfl⟩ := h
  induction l using FreeMonoid.inductionOn' with
  | one => exact one
  | mul_of x y ih =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    refine mul_left _ x.prop (FreeMonoid.lift Subtype.val y) _ (ih ?_)
    simp only [Submonoid.closure_eq_mrange, mem_mrange, exists_apply_eq_apply]

