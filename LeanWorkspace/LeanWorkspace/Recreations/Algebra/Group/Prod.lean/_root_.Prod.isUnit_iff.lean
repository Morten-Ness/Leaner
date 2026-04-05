import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [Monoid M] [Monoid N]

theorem _root_.Prod.isUnit_iff {x : M × N} : IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2 where
  mp h := ⟨(MulEquiv.prodUnits h.unit).1.isUnit, (MulEquiv.prodUnits h.unit).2.isUnit⟩
  mpr h := (MulEquiv.prodUnits.symm (h.1.unit, h.2.unit)).isUnit

