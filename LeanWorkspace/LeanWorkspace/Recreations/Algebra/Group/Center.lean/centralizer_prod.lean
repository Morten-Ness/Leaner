import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem centralizer_prod {N : Type*} [Mul N] {S : Set M} {T : Set N}
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (S ×ˢ T).centralizer = S.centralizer ×ˢ T.centralizer := by
  ext
  simp only [mem_prod, Set.mem_centralizer_iff, Prod.forall, Prod.mul_def]
  grind [Set.Nonempty]

