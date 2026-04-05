import Mathlib

variable {R R' A T B ι : Type*}

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

variable [Semiring R]

variable (degb : A → B) (degt : A → T) (f g : R[A])

theorem sup_support_add_le :
    (f + g).support.sup degb ≤ f.support.sup degb ⊔ g.support.sup degb := by
  classical
  exact (Finset.sup_mono Finsupp.support_add).trans_eq Finset.sup_union

