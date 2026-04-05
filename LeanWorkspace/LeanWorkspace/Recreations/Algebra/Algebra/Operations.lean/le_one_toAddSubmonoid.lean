import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

theorem le_one_toAddSubmonoid : 1 ≤ (1 : Submodule R A).toAddSubmonoid := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, show (n : R) • (1 : A) = n by rw [Nat.cast_smul_eq_nsmul, nsmul_one]⟩

