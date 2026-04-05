import Mathlib

theorem not_isUnit_iff_mk_pos {x : ArchimedeanClass.FiniteElement K} : ¬ IsUnit x ↔ 0 < ArchimedeanClass.FiniteElement.mk x.1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one

