import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [MonoidWithZero α]

variable [PartialOrder α]

theorem MulPosReflectLT.toMulPosReflectLE [IsRightCancelMulZero α] [MulPosReflectLT α] :
    MulPosReflectLE α where
  elim := fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le

