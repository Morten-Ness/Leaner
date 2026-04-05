import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

theorem supDegree_withBot_some_comp {s : AddMonoidAlgebra R A} (hs : s.support.Nonempty) :
    supDegree (WithBot.some ∘ D) s = supDegree D s := by
  unfold AddMonoidAlgebra.supDegree
  rw [← Finset.coe_sup' hs, Finset.sup'_eq_sup]

