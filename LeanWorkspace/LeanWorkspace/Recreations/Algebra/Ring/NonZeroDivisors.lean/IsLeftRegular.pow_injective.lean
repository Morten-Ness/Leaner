import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Monoid R] {r : R}

theorem IsLeftRegular.pow_injective [IsMulTorsionFree R]
    (hx : IsLeftRegular r) (hx' : r ≠ 1) : Function.Injective (fun n ↦ r ^ n) := by
  intro n m hnm
  have main {n m} (h₁ : n ≤ m) (h₂ : r ^ n = r ^ m) : n = m := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h₁
    rw [pow_add, eq_comm, IsLeftRegular.mul_left_eq_self_iff (hx.pow n), pow_eq_one_iff_right hx']
      at h₂
    rw [h₂, Nat.add_zero]
  obtain h | h := Nat.le_or_le n m
  · exact main h hnm
  · exact (main h hnm.symm).symm

