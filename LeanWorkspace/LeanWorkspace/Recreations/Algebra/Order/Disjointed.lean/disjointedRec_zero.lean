import Mathlib

variable {α ι : Type*} [GeneralizedBooleanAlgebra α]

theorem disjointedRec_zero {f : ℕ → α} {p : α → Sort*}
    (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) (h₀ : p (f 0)) :
    Nat.disjointedRec hdiff h₀ = (disjointed_zero f ▸ h₀) := rfl

-- TODO: Find a useful statement of `disjointedRec_succ`.

