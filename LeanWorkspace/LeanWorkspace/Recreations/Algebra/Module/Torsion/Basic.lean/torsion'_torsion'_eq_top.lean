import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (S : Type*) [CommMonoid S] [DistribMulAction S M] [SMulCommClass S R M]

theorem torsion'_torsion'_eq_top : Submodule.torsion' R (Submodule.torsion' R M S) S = ⊤ := (Submodule.isTorsion'_iff_torsion'_eq_top S).mp <| Submodule.torsion'_isTorsion' S

