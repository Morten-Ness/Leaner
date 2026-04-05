import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [Monoid G] [Semiring k] [MulSemiringAction G k]

variable (f g : SkewMonoidAlgebra k G)

variable [DecidableEq G]

theorem support_mul_single_eq_image {r : k} {x : G} (rx : IsRightRegular x)
    (hrx : ∀ g : G, ∀ y, y * g • r = 0 ↔ y = 0) :
    (f * single x r).support = Finset.image (· * x) f.support := by
  refine subset_antisymm (SkewMonoidAlgebra.support_mul_single_subset f _ _) fun y hy ↦ ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ a * x = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, mul_zero,
    ite_self, rx.eq_iff]

