import Mathlib

variable {ι κ M M₀ R : Type*}

variable [Monoid M] [HasDistribNeg M]

theorem prod_map_neg (l : List M) :
    (l.map Neg.neg).prod = (-1) ^ l.length * l.prod := by
  induction l <;> simp [*, pow_succ, ((Commute.neg_one_left _).pow_left _).left_comm]

