import Mathlib

variable {R : Type*}

variable [NonUnitalNonAssocSemiring R]

theorem mulLeft₃_eq_mulRight₃_iff_associative :
    AddMonoidHom.mulLeft₃ (R := R) = AddMonoidHom.mulRight₃ ↔ Std.Associative (fun (x y : R) ↦ x * y) where
  mp h := ⟨fun x y z ↦ by rw [← AddMonoidHom.mulLeft₃_apply, ← AddMonoidHom.mulRight₃_apply, h]⟩
  mpr h := by ext x y z; simp [Std.Associative.assoc]

