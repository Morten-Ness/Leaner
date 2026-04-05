import Mathlib

variable {ι κ M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R]

theorem list_sum_left (b : R) (l : List R) (h : ∀ a ∈ l, Commute a b) : Commute l.sum b := ((Commute.list_sum_right _ _) fun _x hx ↦ (h _ hx).symm).symm

