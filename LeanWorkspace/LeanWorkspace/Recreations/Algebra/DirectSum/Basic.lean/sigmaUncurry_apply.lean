import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι] {α : ι → Type u} {δ : ∀ i, α i → Type w} [∀ i j, AddCommMonoid (δ i j)]

theorem sigmaUncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) :
    DirectSum.sigmaUncurry f ⟨i, j⟩ = f i j := DFinsupp.sigmaUncurry_apply f i j

