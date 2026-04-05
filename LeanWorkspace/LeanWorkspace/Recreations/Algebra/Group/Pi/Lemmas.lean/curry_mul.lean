import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

theorem curry_mul [∀ a b, Mul (γ a b)] (x y : (i : Σ a, β a) → γ i.1 i.2) :
    Sigma.curry (x * y) = Sigma.curry x * Sigma.curry y := rfl

