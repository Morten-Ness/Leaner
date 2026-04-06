import Mathlib

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

variable (S : Type*) [Semiring S] [Algebra R S]

theorem funUnique_apply [Unique ι] (x : ι → S) : AlgEquiv.funUnique R ι S x = Equiv.funUnique ι S x := rfl
