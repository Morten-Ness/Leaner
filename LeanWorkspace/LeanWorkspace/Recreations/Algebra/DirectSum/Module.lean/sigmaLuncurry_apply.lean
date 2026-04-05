import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {α : ι → Type*} {δ : ∀ i, α i → Type w}

variable [DecidableEq ι] [∀ i j, AddCommMonoid (δ i j)] [∀ i j, Module R (δ i j)]

theorem sigmaLuncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) :
    DirectSum.sigmaLuncurry R f ⟨i, j⟩ = f i j := sigmaUncurry_apply f i j

