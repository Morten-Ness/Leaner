import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_mul_eq_left {f g : α → M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport f).mulIndicator (f * g) = f := by
  refine (mulIndicator_congr fun x hx => ?_).trans mulIndicator_mulSupport
  have : g x = 1 := notMem_mulSupport.1 (disjoint_left.1 h hx)
  rw [Pi.mul_apply, this, mul_one]

