import Mathlib

variable {R R' A T B ι : Type*}

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

variable [Semiring R]

variable (degb : A → B) (degt : A → T) (f g : R[A])

theorem le_inf_support_add : f.support.inf degt ⊓ g.support.inf degt ≤ (f + g).support.inf degt := AddMonoidAlgebra.sup_support_add_le (fun a : A => OrderDual.toDual (degt a)) f g

