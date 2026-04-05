import Mathlib

variable {α β M N : Type*}

variable {G : Type*} [Group G] {s t : Set α}

theorem mulIndicator_diff' (h : s ⊆ t) (f : α → G) :
    mulIndicator (t \ s) f = mulIndicator t f / mulIndicator s f := by
  rw [Set.mulIndicator_diff h, div_eq_mul_inv]

