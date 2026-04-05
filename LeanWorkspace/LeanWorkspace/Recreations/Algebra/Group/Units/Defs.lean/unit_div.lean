import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [DivisionMonoid α] {a b c : α}

theorem unit_div (ha : IsUnit a) (hb : IsUnit b) : (IsUnit.div ha hb).unit = ha.unit / hb.unit := Units.ext (Units.val_div_eq_div_val ha.unit hb.unit).symm

