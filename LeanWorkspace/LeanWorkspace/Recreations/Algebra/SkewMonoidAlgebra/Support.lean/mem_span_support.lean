import Mathlib

open scoped Pointwise

variable {k G : Type*}

variable [Monoid G] [Semiring k] [MulSemiringAction G k]

variable (f g : SkewMonoidAlgebra k G)

theorem mem_span_support (f : SkewMonoidAlgebra k G) :
    f ∈ Submodule.span k (of k G '' (f.support : Set G)) := by
  rw [Fintype.mem_span_image_iff_exists_fun k]
  use Finset.restrict f.support f.coeff
  simp [smul_single, ← sum_def', sum_single]

