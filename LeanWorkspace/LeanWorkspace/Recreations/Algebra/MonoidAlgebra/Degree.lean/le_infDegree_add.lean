import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeInf T] [OrderTop T] (D : A → T)

theorem le_infDegree_add (f g : R[A]) :
    (f.infDegree D) ⊓ (g.infDegree D) ≤ (f + g).infDegree D := AddMonoidAlgebra.le_inf_support_add D f g

