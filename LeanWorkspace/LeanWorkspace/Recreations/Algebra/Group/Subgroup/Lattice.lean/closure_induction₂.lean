import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_induction₂ {p : (x y : G) → x ∈ Subgroup.closure k → y ∈ Subgroup.closure k → Prop}
    (mem : ∀ (x) (y) (hx : x ∈ k) (hy : y ∈ k), p x y (Subgroup.subset_closure hx) (Subgroup.subset_closure hy))
    (one_left : ∀ x hx, p 1 x (one_mem _) hx) (one_right : ∀ x hx, p x 1 hx (one_mem _))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ y z x hy hz hx, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    (inv_left : ∀ x y hx hy, p x y hx hy → p x⁻¹ y (inv_mem hx) hy)
    (inv_right : ∀ x y hx hy, p x y hx hy → p x y⁻¹ hx (inv_mem hy))
    {x y : G} (hx : x ∈ Subgroup.closure k) (hy : y ∈ Subgroup.closure k) : p x y hx hy := by
  induction hy using Subgroup.closure_induction with
  | mem z hz => induction hx using Subgroup.closure_induction with
    | mem _ h => exact mem _ _ h hz
    | one => exact one_left _ (Subgroup.subset_closure hz)
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | inv _ _ h => exact inv_left _ _ _ _ h
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ hx h₁ h₂
  | inv _ _ h => exact inv_right _ _ _ _ h

