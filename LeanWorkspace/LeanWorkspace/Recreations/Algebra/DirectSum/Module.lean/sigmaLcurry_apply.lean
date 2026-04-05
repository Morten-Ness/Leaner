import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {α : ι → Type*} {δ : ∀ i, α i → Type w}

variable [DecidableEq ι] [∀ i j, AddCommMonoid (δ i j)] [∀ i j, Module R (δ i j)]

theorem sigmaLcurry_apply (f : ⨁ i : Σ _, _, δ i.1 i.2) (i : ι) (j : α i) :
    DirectSum.sigmaLcurry R f i j = f ⟨i, j⟩ := sigmaCurry_apply f i j

