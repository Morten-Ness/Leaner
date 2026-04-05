import Mathlib

section

variable {ι κ M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R]

theorem list_sum_left (b : R) (l : List R) (h : ∀ a ∈ l, Commute a b) : Commute l.sum b := ((Commute.list_sum_right _ _) fun _x hx ↦ (h _ hx).symm).symm

end

section

variable {ι κ M M₀ R : Type*}

variable [Monoid M] [HasDistribNeg M]

theorem prod_map_neg (l : List M) :
    (l.map Neg.neg).prod = (-1) ^ l.length * l.prod := by
  induction l <;> simp [*, pow_succ, ((Commute.neg_one_left _).pow_left _).left_comm]

end
