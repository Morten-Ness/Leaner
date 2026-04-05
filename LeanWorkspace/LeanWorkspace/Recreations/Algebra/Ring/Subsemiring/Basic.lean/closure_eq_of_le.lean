import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_eq_of_le {s : Set R} {t : Subsemiring R} (h₁ : s ⊆ t) (h₂ : t ≤ Subsemiring.closure s) :
    Subsemiring.closure s = t := le_antisymm (Subsemiring.closure_le.2 h₁) h₂

