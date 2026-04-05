import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_eq_iff : toIocMod hp a b = c ↔ c ∈ Set.Ioc a (a + p) ∧ ∃ z : ℤ, b = c + z • p := by
  refine
    ⟨fun h =>
      ⟨h ▸ toIocMod_mem_Ioc hp a b, toIocDiv hp a b, h ▸ (toIocMod_add_toIocDiv_zsmul hp _ _).symm⟩,
      ?_⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIocDiv_eq_of_sub_zsmul_mem_Ioc hp hc, toIocMod]

