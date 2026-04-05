import Mathlib

variable {ι F M N O G H : Type*}

variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

theorem support_sub [DecidableEq ι] {f g : ι →₀ G} : support (f - g) ⊆ support f ∪ support g := by
  rw [sub_eq_add_neg, ← Finsupp.support_neg g]
  exact Finsupp.support_add

