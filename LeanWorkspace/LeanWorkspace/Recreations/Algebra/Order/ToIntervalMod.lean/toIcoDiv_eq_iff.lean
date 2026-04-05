import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_eq_iff : toIcoDiv hp a b = n ↔ b - n • p ∈ Set.Ico a (a + p) := (existsUnique_sub_zsmul_mem_Ico hp b a).choose_eq_iff

alias ⟨_, toIcoDiv_eq_of_sub_zsmul_mem_Ico⟩ := toIcoDiv_eq_iff

