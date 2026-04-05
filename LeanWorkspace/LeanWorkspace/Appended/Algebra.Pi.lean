import Mathlib

section

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

variable (S : Type*) [Semiring S] [Algebra R S]

theorem funUnique_apply [Unique ι] (x : ι → S) : AlgEquiv.funUnique R ι S x = Equiv.funUnique ι S x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first

end

section

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

theorem piCongrLeft'_apply {ι' : Type*} (e : ι ≃ ι') (x : (Π i, A₁ i)) :
    AlgEquiv.piCongrLeft' R A₁ e x = Equiv.piCongrLeft' _ _ x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first

end

section

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

theorem piCongrLeft_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ (e i)) :
    AlgEquiv.piCongrLeft R A₁ e x = Equiv.piCongrLeft _ _ x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first

end

section

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}

variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]

variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

variable (S : Type*) [Semiring S] [Algebra R S]

theorem sumArrowEquivProdArrow_apply (x : α ⊕ β → S) :
    AlgEquiv.sumArrowEquivProdArrow α β R S x = Equiv.sumArrowEquivProdArrow α β S x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first

end
