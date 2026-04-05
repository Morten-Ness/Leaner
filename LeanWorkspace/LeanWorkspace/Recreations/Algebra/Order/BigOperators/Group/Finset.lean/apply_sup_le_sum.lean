import Mathlib

variable {ι α β M N G k R : Type*}

theorem apply_sup_le_sum [SemilatticeSup α] [OrderBot α]
    [AddCommMonoid β] [Preorder β] [AddLeftMono β]
    {f : α → β} (zero : f ⊥ = 0) (ih : ∀ {s t}, f (s ⊔ t) ≤ f s + f t)
    {s : ι → α} (t : Finset ι) :
    f (t.sup s) ≤ ∑ i ∈ t, f (s i) := by
  classical
  refine t.induction_on zero.le fun i t it h ↦ ?_
  simpa only [sup_insert, Finset.sum_insert it] using ih.trans (by gcongr)

