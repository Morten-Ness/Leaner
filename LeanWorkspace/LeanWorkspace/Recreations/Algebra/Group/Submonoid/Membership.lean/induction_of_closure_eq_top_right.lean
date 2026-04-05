import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem induction_of_closure_eq_top_right {s : Set M} {motive : M → Prop} (hs : closure s = ⊤)
    (x : M) (one : motive 1) (mul_right : ∀ x, ∀ y ∈ s, motive x → motive (x * y)) : motive x := by
  have : x ∈ closure s := by simp [hs]
  induction this using Submonoid.closure_induction_right with
  | one => exact one
  | mul_right x _ y hy ih => exact mul_right x y hy ih

