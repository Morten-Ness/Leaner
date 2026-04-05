import Mathlib

variable {F α β γ : Type*}

variable [CommRing α] [IsDomain α] [CommRing β] (f : β →+ α)

theorem coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β →+ α) = f := by
  ext
  rfl

