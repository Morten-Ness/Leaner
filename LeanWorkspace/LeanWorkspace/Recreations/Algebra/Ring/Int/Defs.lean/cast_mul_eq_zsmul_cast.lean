import Mathlib

theorem cast_mul_eq_zsmul_cast {α : Type*} [AddGroupWithOne α] :
    ∀ m n : ℤ, ↑(m * n) = m • (n : α) := fun m ↦ Int.induction_on m (by simp) (fun _ ih ↦ by simp [add_mul, add_zsmul, ih]) fun _ ih ↦ by
    simp only [sub_mul, one_mul, cast_sub, ih, sub_zsmul, one_zsmul, ← sub_eq_add_neg, forall_const]

