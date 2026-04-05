import Mathlib

variable {α ι : Type*} [SemilatticeSup α] [LinearOrder ι]

theorem partialSups_succ' {α : Type*} [SemilatticeSup α] [LocallyFiniteOrder ι]
    [SuccOrder ι] [OrderBot ι] (f : ι → α) (i : ι) :
    (partialSups f) (Order.succ i) = f ⊥ ⊔ (partialSups (f ∘ Order.succ)) i := by
  refine Succ.rec (by simp) (fun j _ h ↦ ?_) (bot_le (a := i))
  have : (partialSups (f ∘ Order.succ)) (Order.succ j) =
      ((partialSups (f ∘ Order.succ)) j ⊔ (f ∘ Order.succ) (Order.succ j)) := by simp
  simp [this, h, sup_assoc]

