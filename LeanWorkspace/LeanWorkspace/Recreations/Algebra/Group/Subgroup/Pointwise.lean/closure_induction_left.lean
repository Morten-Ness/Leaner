import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem closure_induction_left {p : (x : G) → x ∈ closure s → Prop} (one : p 1 (one_mem _))
    (mul_left : ∀ x (hx : x ∈ s), ∀ (y) hy, p y hy → p (x * y) (mul_mem (subset_closure hx) hy))
    (inv_mul_cancel : ∀ x (hx : x ∈ s), ∀ (y) hy, p y hy →
      p (x⁻¹ * y) (mul_mem (inv_mem (subset_closure hx)) hy))
    {x : G} (h : x ∈ closure s) : p x h := by
  revert h
  simp_rw [← mem_toSubmonoid, Subgroup.closure_toSubmonoid] at *
  intro h
  induction h using Submonoid.closure_induction_left with
  | one => exact one
  | mul_left x hx y hy ih =>
    cases hx with
    | inl hx => exact mul_left _ hx _ hy ih
    | inr hx => simpa only [inv_inv] using inv_mul_cancel _ hx _ hy ih

