import Mathlib

variable [GroupWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

theorem valueMonoid_eq_valueGroup : (MonoidWithZeroHom.valueMonoid f) = (MonoidWithZeroHom.valueGroup f).toSubmonoid := by
  rw [MonoidWithZeroHom.valueGroup_def, Subgroup.closure_toSubmonoid, Eq.comm]
  apply Submonoid.closure_eq_of_le
  · simp only [union_subset_iff, subset_refl, true_and]
    intro _ ⟨y, hy⟩
    use y⁻¹
    simp [hy]
  · simp [Submonoid.closure_union]

