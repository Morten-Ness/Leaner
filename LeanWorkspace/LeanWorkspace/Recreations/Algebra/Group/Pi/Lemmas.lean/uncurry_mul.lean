import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

theorem uncurry_mul [∀ a b, Mul (γ a b)] (x y : ∀ a b, γ a b) :
    Sigma.uncurry (x * y) = Sigma.uncurry x * Sigma.uncurry y := rfl

