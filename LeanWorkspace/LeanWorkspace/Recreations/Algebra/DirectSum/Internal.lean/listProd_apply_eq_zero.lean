import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedAddMonoid ι] [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R]

variable {A : ι → σ} [SetLike.GradedMonoid A]

variable [CanonicallyOrderedAdd ι]

theorem listProd_apply_eq_zero {l : List (⨁ i, A i)} {m : ι}
    (hl : ∀ x ∈ l, ∀ k < m, x k = 0) ⦃n : ι⦄ (hn : n < l.length • m) :
    l.prod n = 0 := by
  -- a proof which uses `DirectSum.listProd_apply_eq_zero'` is actually more work
  induction l generalizing n with
  | nil => simp [(zero_le n).not_gt] at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.length_cons, List.prod_cons] at hl hn ⊢
    refine mul_apply_eq_zero hl.1 (ih hl.2) ?_
    simpa [add_smul, add_comm m] using hn

