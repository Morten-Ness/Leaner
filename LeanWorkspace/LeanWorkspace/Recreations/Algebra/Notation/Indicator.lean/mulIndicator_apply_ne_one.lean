import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_apply_ne_one {a : α} : s.mulIndicator f a ≠ 1 ↔ a ∈ s ∩ mulSupport f := by
  simp only [Ne, Set.mulIndicator_apply_eq_one, Classical.not_imp, mem_inter_iff, mem_mulSupport]

