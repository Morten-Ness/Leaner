import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

variable {γ : Type u₁} [AddCommMonoid γ]

variable (φ : ∀ i, β i →+ γ) (ψ : (⨁ i, β i) →+ γ)

theorem toAddMonoid_injective : Function.Injective (DirectSum.toAddMonoid : (∀ i, β i →+ γ) → (⨁ i, β i) →+ γ) := DFinsupp.liftAddHom.injective

