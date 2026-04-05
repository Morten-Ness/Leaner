import Mathlib

variable {R : Type*}

variable [NonUnitalSemiring R]

theorem mulLeft₃_eq_mulRight₃ : AddMonoidHom.mulLeft₃ (R := R) = AddMonoidHom.mulRight₃ :=
  AddMonoidHom.mulLeft₃_eq_mulRight₃_iff_associative.2 inferInstance

