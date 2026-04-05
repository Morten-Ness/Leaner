import Mathlib

variable {F ι κ G M N O : Type*}

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι → G}

theorem prod_map_inv' (m : Multiset G) : (m.map Inv.inv).prod = m.prod⁻¹ := Multiset.prod_hom m (invMonoidHom : G →* G)

