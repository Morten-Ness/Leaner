import Mathlib

variable {F ι κ G M N O : Type*}

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι → G}

theorem prod_map_zpow {n : ℤ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n := by
  convert Multiset.prod_hom (m.map f) (zpowGroupHom n : G →* G)
  simp only [map_map, Function.comp_apply, zpowGroupHom_apply]

