import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

theorem curry_one [∀ a b, One (γ a b)] : Sigma.curry (1 : (i : Σ a, β a) → γ i.1 i.2) = 1 := rfl

