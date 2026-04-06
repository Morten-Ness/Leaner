import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

variable {γ : Type u₁} [AddCommMonoid γ]

theorem fromAddMonoid_of_apply (i : ι) (f : γ →+ β i) (x : γ) :
    DirectSum.fromAddMonoid (DirectSum.of _ i f) x = DirectSum.of _ i (f x) := by
  simp [DirectSum.fromAddMonoid]
