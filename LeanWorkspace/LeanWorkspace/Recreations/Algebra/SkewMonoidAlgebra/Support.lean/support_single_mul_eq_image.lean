import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [Monoid G] [Semiring k] [MulSemiringAction G k]

variable (f g : SkewMonoidAlgebra k G)

variable [DecidableEq G]

theorem support_single_mul_eq_image {r : k} {x : G} (lx : IsLeftRegular x)
    (hrx : ∀ y, r * x • y = 0 ↔ y = 0) :
    (single x r * f : SkewMonoidAlgebra k G).support = Finset.image (x * ·) f.support := by
  refine subset_antisymm (SkewMonoidAlgebra.support_single_mul_subset f _ _) fun y hy ↦ ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ x * a = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, Ne,
    zero_mul, ite_self, sum_zero, lx.eq_iff]

