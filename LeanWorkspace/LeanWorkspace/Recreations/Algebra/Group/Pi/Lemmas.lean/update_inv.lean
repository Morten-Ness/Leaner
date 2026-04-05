import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

theorem update_inv [∀ i, Inv (f i)] [DecidableEq I] (f₁ : ∀ i, f i) (i : I) (x₁ : f i) :
    Function.update f₁⁻¹ i x₁⁻¹ = (Function.update f₁ i x₁)⁻¹ := funext fun j => (apply_update (fun _ => Inv.inv) f₁ i x₁ j).symm

