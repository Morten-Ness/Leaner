import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrderTop α]

variable [Add α] [SuccAddOrder α] {a : α}

theorem Ici_add_one_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (a + 1) = Ioi a := by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi_of_not_isMax ha

