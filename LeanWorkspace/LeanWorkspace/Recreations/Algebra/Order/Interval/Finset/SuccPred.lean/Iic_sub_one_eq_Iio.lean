import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrderBot α]

variable [Sub α] [PredSubOrder α] {a b : α}

variable [NoMinOrder α]

theorem Iic_sub_one_eq_Iio (b : α) : Iic (b - 1) = Iio b := by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio b

