FAIL
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
  revert y hy
  refine Subgroup.closure_induction hx ?hmem ?hone ?hmul ?hinv
  · intro x hxk y hy
    revert x hxk
    refine Subgroup.closure_induction hy ?hmem₂ ?hone₂ ?hmul₂ ?hinv₂
    · intro y hyk x hxk
      exact mem x y hxk hyk
    · intro x hxk
      exact one_right x (Subgroup.subset_closure hxk)
    · intro a b ha hb iha ihb x hxk
      exact mul_right a b x ha hb (Subgroup.subset_closure hxk) (iha x hxk) (ihb x hxk)
    · intro a ha iha x hxk
      exact inv_right x a (Subgroup.subset_closure hxk) ha (iha x hxk)
  · intro y hy
    exact one_left y hy
  · intro a b ha hb iha ihb y hy
    exact mul_left a b y ha hb hy (iha y hy) (ihb y hy)
  · intro a ha iha y hy
    exact inv_left a y ha hy (iha y hy)
