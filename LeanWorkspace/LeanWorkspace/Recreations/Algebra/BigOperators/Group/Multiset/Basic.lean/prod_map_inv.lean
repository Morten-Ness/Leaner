import Mathlib

variable {F ι κ G M N O : Type*}

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι → G}

theorem prod_map_inv : (m.map fun i => (f i)⁻¹).prod = (m.map f).prod⁻¹ := by
  rw [← Multiset.prod_map_inv' (m.map f), map_map, Function.comp_def]

