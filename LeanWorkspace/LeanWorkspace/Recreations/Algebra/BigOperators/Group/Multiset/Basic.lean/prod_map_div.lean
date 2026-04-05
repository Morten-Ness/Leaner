import Mathlib

variable {F ι κ G M N O : Type*}

variable [DivisionCommMonoid G] {m : Multiset ι} {f g : ι → G}

theorem prod_map_div : (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod := Multiset.prod_hom₂ m (· / ·) mul_div_mul_comm (div_one _) _ _

