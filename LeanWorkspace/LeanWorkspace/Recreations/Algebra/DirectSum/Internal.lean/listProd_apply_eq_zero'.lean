import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedAddMonoid ι] [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R]

variable {A : ι → σ} [SetLike.GradedMonoid A]

variable [CanonicallyOrderedAdd ι]

theorem listProd_apply_eq_zero' {l : List ((⨁ i, A i) × ι)}
    (hl : ∀ xn ∈ l, ∀ k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < (l.map Prod.snd).sum) :
    (l.map Prod.fst).prod n = 0 := by
  induction l generalizing n with
  | nil => simp [(zero_le n).not_gt] at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, List.sum_cons,
      List.prod_cons] at hl hn ⊢
    exact mul_apply_eq_zero hl.1 (ih hl.2) hn

