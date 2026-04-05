import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

variable {p q : R[A]}

variable [AddZeroClass A]

variable [Add B]

theorem supDegree_mul_le (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftMono B] [AddRightMono B] :
    (p * q).supDegree D ≤ p.supDegree D + q.supDegree D := AddMonoidAlgebra.sup_support_mul_le (fun {_ _} => (hadd _ _).le) p q

