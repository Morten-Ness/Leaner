import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

theorem supDegree_eq_of_isMaxOn {p : R[A]} {a : A} (hmem : a ∈ p.support)
    (hmax : IsMaxOn D p.support a) : p.supDegree D = D a := sup_eq_of_isMaxOn hmem hmax

