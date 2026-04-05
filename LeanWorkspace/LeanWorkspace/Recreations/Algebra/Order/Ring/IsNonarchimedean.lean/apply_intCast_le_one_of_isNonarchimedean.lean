import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem apply_intCast_le_one_of_isNonarchimedean [IsStrictOrderedRing R]
    {F α : Type*} [AddGroupWithOne α] [FunLike F α R]
    [AddGroupSeminormClass F α R] [OneHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : ℤ} : f n ≤ 1 := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n <;>
  simp [IsNonarchimedean.apply_natCast_le_one_of_isNonarchimedean hna]

set_option linter.style.whitespace false in -- manual alignment is not recognised

