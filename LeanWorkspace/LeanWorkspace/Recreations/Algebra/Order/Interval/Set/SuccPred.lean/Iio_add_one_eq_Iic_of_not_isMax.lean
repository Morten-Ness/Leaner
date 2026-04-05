import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Add α] [SuccAddOrder α] {b : α}

theorem Iio_add_one_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (b + 1) = Iic b := by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic_of_not_isMax hb

