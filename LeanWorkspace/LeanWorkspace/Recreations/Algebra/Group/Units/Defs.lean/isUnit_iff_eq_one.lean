import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [Monoid M] {a b : M}

variable [Subsingleton Mˣ]

theorem isUnit_iff_eq_one : IsUnit a ↔ a = 1 where
  mp := IsUnit.eq_one
  mpr := by rintro rfl; exact isUnit_one

