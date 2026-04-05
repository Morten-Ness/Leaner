import Mathlib

variable {F α β R S S' : Type*}

theorem isDomain_iff {A B : Type*} [Semiring A] [Semiring B] (e : A ≃* B) :
    IsDomain A ↔ IsDomain B where
  mp _ := MulEquiv.isDomain e.symm
  mpr _ := MulEquiv.isDomain e

