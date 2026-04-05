import Mathlib

variable {ι F M N O G H : Type*}

variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

theorem support_neg (f : ι →₀ G) : support (-f) = support f := Finset.Subset.antisymm support_mapRange
    (calc
      support f = support (- -f) := congr_arg support (neg_neg _).symm
      _ ⊆ support (-f) := support_mapRange)

