import Mathlib

open scoped Pointwise

variable {k : Type u₁} {G : Type u₂} [Semiring k]

set_option backward.isDefEq.respectTransparency false in
theorem mem_span_support (f : k[G]) : f ∈ Submodule.span k (of' k G '' f.support) := by
  simp only [of']; rw [← Finsupp.supported_eq_span_single, Finsupp.mem_supported]

