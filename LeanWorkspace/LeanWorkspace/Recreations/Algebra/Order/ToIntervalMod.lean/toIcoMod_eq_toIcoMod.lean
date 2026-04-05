import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_eq_toIcoMod : toIcoMod hp a b = toIcoMod hp a c ↔ ∃ n : ℤ, c - b = n • p := by
  refine ⟨fun h => ⟨toIcoDiv hp a c - toIcoDiv hp a b, ?_⟩, fun h => ?_⟩
  · conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hp a b, ← toIcoMod_add_toIcoDiv_zsmul hp a c]
    rw [h, sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz, toIcoMod_zsmul_add]

