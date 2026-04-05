import Mathlib

variable [GroupWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

variable [MonoidWithZero A] [CommGroupWithZero B] [MonoidWithZeroHomClass F A B]

theorem mk_eq_of_ne_zero [DecidablePred fun b : B ↦ b = 0] (r s : A) (hr : f r ≠ 0) (hs : f s ≠ 0) :
    ValueGroup₀.mk f r s = MonoidWithZeroHom.valueGroup.mk f r s hr hs := by
  simp [ValueGroup₀.mk, hr, hs]

