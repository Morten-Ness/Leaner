import Mathlib

variable {α ι : Type*} [SemilatticeSup α] [LinearOrder ι]

theorem partialSups_add_one [Add ι] [One ι] [LocallyFiniteOrderBot ι] [SuccAddOrder ι]
    (f : ι → α) (i : ι) : partialSups f (i + 1) = partialSups f i ⊔ f (i + 1) := Order.succ_eq_add_one i ▸ partialSups_succ f i

