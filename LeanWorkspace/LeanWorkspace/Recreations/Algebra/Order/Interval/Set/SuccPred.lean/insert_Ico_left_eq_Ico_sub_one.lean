import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Sub α] [PredSubOrder α] {a b : α}

variable [NoMinOrder α]

theorem insert_Ico_left_eq_Ico_sub_one (h : a ≤ b) : insert (a - 1) (Ico a b) = Ico (a - 1) b := Set.insert_Ico_left_eq_Ico_sub_one_of_not_isMin h (not_isMin _)

