import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeInf T] [OrderTop T] (D : A → T)

theorem infDegree_withTop_some_comp {s : AddMonoidAlgebra R A} (hs : s.support.Nonempty) :
    infDegree (WithTop.some ∘ D) s = infDegree D s := by
  unfold AddMonoidAlgebra.infDegree
  rw [← Finset.coe_inf' hs, Finset.inf'_eq_inf]

