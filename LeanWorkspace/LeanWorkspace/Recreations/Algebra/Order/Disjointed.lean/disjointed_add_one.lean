import Mathlib

variable {α ι : Type*} [GeneralizedBooleanAlgebra α]

variable [LinearOrder ι] [LocallyFiniteOrderBot ι] [Add ι] [One ι] [SuccAddOrder ι]

theorem disjointed_add_one [NoMaxOrder ι] (f : ι → α) (i : ι) :
    disjointed f (i + 1) = f (i + 1) \ partialSups f i := by
  simpa only [succ_eq_add_one] using disjointed_succ f (not_isMax i)

