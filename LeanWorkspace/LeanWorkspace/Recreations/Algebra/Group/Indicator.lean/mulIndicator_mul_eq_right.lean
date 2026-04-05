import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_mul_eq_right {f g : α → M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport g).mulIndicator (f * g) = g := by
  refine (mulIndicator_congr fun x hx => ?_).trans mulIndicator_mulSupport
  have : f x = 1 := notMem_mulSupport.1 (disjoint_right.1 h hx)
  rw [Pi.mul_apply, this, one_mul]

