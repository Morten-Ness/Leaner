import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_eq_iff : toIcoMod hp a b = c ↔ c ∈ Set.Ico a (a + p) ∧ ∃ z : ℤ, b = c + z • p := by
  refine
    ⟨fun h =>
      ⟨h ▸ toIcoMod_mem_Ico hp a b, toIcoDiv hp a b, h ▸ (toIcoMod_add_toIcoDiv_zsmul _ _ _).symm⟩,
      ?_⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIcoDiv_eq_of_sub_zsmul_mem_Ico hp hc, toIcoMod]

