import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem induction_linear {p : R[M] → Prop} (x : R[M]) (zero : p 0)
    (add : ∀ x y : R[M], p x → p y → p (x + y)) (single : ∀ m r, p (single m r)) :
    p x := Finsupp.induction_linear x zero (fun _ _ ↦ add _ _) (fun _ _ ↦ single _ _)

