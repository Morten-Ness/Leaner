import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_eq_iff : toIocDiv hp a b = n ↔ b - n • p ∈ Set.Ioc a (a + p) := (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_eq_iff

alias ⟨_, toIocDiv_eq_of_sub_zsmul_mem_Ioc⟩ := toIocDiv_eq_iff

