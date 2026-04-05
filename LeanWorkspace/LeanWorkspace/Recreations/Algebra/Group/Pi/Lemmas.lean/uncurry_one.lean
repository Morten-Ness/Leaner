import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

theorem uncurry_one [∀ a b, One (γ a b)] : Sigma.uncurry (1 : ∀ a b, γ a b) = 1 := rfl

