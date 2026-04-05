import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

theorem update_mul [∀ i, Mul (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : Function.update (f₁ * f₂) i (x₁ * x₂) = Function.update f₁ i x₁ * Function.update f₂ i x₂ := funext fun j => (apply_update₂ (fun _ => (· * ·)) f₁ f₂ i x₁ x₂ j).symm

