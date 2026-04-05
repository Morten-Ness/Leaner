import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [IsCancelMulZero α]

variable (G₀ : Type*) [CommGroupWithZero G₀] [DecidableEq G₀]

private theorem map_mk_unit_aux {f : Associates α →* α}
    (hinv : Function.RightInverse f Associates.mk) (a : α) :
    a * ↑(Classical.choose (associated_map_mk hinv a)) = f (Associates.mk a) := Classical.choose_spec (associated_map_mk hinv a)


theorem coe_normUnit {a : G₀} (h0 : a ≠ 0) : (↑(normUnit a) : G₀) = a⁻¹ := by simp [normUnit, h0]

