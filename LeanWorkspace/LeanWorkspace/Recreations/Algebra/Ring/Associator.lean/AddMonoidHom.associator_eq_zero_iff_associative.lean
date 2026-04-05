import Mathlib

variable {R : Type*}

variable [NonUnitalNonAssocRing R] (a b c : R)

theorem associator_eq_zero_iff_associative :
    AddMonoidHom.associator (R := R) = 0 ↔ Std.Associative (fun (x y : R) ↦ x * y) := by
  simp [AddMonoidHom.mulLeft₃_eq_mulRight₃_iff_associative, AddMonoidHom.associator, sub_eq_zero]

