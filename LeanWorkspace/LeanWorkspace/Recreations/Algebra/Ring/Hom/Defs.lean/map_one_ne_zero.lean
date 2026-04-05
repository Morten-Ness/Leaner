import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem map_one_ne_zero [Nontrivial β] : f 1 ≠ 0 := mt RingHom.codomain_trivial_iff_map_one_eq_zero f.mpr zero_ne_one

