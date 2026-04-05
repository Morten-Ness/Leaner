import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem prod_centralizer_subset_centralizer_prod {N : Type*} [Mul N] (S : Set M) (T : Set N) :
    S.centralizer ×ˢ T.centralizer ⊆ (S ×ˢ T).centralizer := by
  simp_all [subset_def, Set.mem_centralizer_iff]

