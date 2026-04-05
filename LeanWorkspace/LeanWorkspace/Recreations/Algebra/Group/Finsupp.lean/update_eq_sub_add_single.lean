import Mathlib

variable {ι F M N O G H : Type*}

variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

theorem update_eq_sub_add_single (f : ι →₀ G) (a : ι) (b : G) :
    f.update a b = f - single a (f a) + single a b := by
  rw [Finsupp.update_eq_erase_add_single, Finsupp.erase_eq_sub_single]

