import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

variable {γ : Type u₁} [AddCommMonoid γ]

variable (φ : ∀ i, β i →+ γ) (ψ : (⨁ i, β i) →+ γ)

theorem toAddMonoid_of (i) (x : β i) : DirectSum.toAddMonoid φ (DirectSum.of β i x) = φ i x := DFinsupp.liftAddHom_apply_single φ i x

