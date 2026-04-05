import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

variable {R S : Type*} [Semiring R] [Semiring S] [Module R M] [Module S M]
  [DistribSMul S R] [SMulCommClass R S M] [IsScalarTower S R M] (f : End R M)

theorem invtSubmodule_le_invtSubmodule_smul (c : S) : f.invtSubmodule ≤ (c • f).invtSubmodule := fun p hfp _ hx ↦ p.smul_of_tower_mem c (hfp hx)

