import Mathlib

variable {M N G H α β γ δ : Type*}

variable [SMul M α]

theorem Commute.smul_left [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute (r • a) b := (h.symm.smul_right r).symm

