import Mathlib

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

variable (S : Type*) [Semiring S] [Algebra R S]

theorem sumArrowEquivProdArrow_symm_apply_inr (x : (α → S) × (β → S)) :
    (AlgEquiv.sumArrowEquivProdArrow α β R S).symm x = (Equiv.sumArrowEquivProdArrow α β S).symm x := rfl

