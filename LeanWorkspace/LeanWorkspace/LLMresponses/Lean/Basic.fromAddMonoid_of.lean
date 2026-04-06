FAIL
import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

variable {γ : Type u₁} [AddCommMonoid γ]

theorem fromAddMonoid_of (i : ι) (f : γ →+ β i) : DirectSum.fromAddMonoid (DirectSum.of _ i f) = (DirectSum.of _ i).comp f := by
  ext x j
  simp [DirectSum.fromAddMonoid, DirectSum.of, DFinsupp.singleAddHom]
