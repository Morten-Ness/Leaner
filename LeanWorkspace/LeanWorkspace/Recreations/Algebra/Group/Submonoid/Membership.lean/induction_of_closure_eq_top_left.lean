import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem induction_of_closure_eq_top_left {s : Set M} {motive : M → Prop} (hs : closure s = ⊤)
    (x : M) (one : motive 1) (mul_left : ∀ x ∈ s, ∀ y, motive y → motive (x * y)) : motive x := by
  have : x ∈ closure s := by simp [hs]
  induction this using Submonoid.closure_induction_left with
  | one => exact one
  | mul_left x hx y _ ih => exact mul_left x hx y ih

