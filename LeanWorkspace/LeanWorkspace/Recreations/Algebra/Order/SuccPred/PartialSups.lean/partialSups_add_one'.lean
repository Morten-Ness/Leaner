import Mathlib

variable {α ι : Type*} [SemilatticeSup α] [LinearOrder ι]

theorem partialSups_add_one' [Add ι] [One ι] [OrderBot ι] [LocallyFiniteOrder ι]
    [SuccAddOrder ι] (f : ι → α) (i : ι) :
    partialSups f (i + 1) = f ⊥ ⊔ partialSups (f ∘ (fun k ↦ k + 1)) i := by
  simpa [← Order.succ_eq_add_one] using partialSups_succ' f i

