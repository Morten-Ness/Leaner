import Mathlib

section

variable {M G : Type*}

variable [Group G] [IsMulTorsionFree G] {n : ℤ} {a b : G}

theorem IsMulTorsionFree.zpow_eq_one_iff : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [zpow_eq_one_iff_left, *]

end

section

variable {M G : Type*}

variable [Group G] [IsMulTorsionFree G] {n : ℤ} {a b : G}

theorem IsMulTorsionFree.zpow_eq_one_iff_left (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  rw [← zpow_left_inj (a := a) hn, one_zpow]

-- We want to use `IsAddTorsion.zsmul_eq_zero_iff` earlier than `smul_eq_zero`.

end

section

variable {M G : Type*}

variable [Monoid M]

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

theorem pow_eq_one_iff : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [pow_eq_one_iff_left, *]

end

section

variable {M G : Type*}

variable [Monoid M]

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

theorem pow_eq_one_iff_left (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  rw [← pow_left_inj (a := a) hn, one_pow]

-- We want to use `IsAddTorsion.nsmul_eq_zero_iff` earlier than `smul_eq_zero`.

end

section

variable {M G : Type*}

variable [Monoid M]

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

theorem pow_left_injective (hn : n ≠ 0) : Function.Injective fun a : M ↦ a ^ n := IsMulTorsionFree.pow_left_injective hn

end
