import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

set_option backward.isDefEq.respectTransparency false in
theorem toQuotient_relation (r : relations.R) :
    relations.toQuotient (relations.relation r) = 0 := by
  dsimp only [Module.Relations.toQuotient, Module.Relations.Quotient]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (by simp)

