import Mathlib

variable {R : Type*}

variable [NonUnitalNonAssocRing R]

theorem associator_eq_zero_iff_associative :
    associator (R := R) = 0 ↔ Std.Associative (fun (x y : R) ↦ x * y) where
  mp h := ⟨fun x y z ↦ sub_eq_zero.mp <| congr_fun₃ h x y z⟩
  mpr h := by ext x y z; simp [associator, Std.Associative.assoc]

