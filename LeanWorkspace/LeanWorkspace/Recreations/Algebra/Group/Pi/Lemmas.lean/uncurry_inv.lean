import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

theorem uncurry_inv [∀ a b, Inv (γ a b)] (x : ∀ a b, γ a b) :
    Sigma.uncurry (x⁻¹) = (Sigma.uncurry x)⁻¹ := rfl

