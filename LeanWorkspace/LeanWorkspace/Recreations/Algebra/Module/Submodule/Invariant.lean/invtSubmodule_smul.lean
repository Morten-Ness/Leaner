import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

variable {R S : Type*} [Semiring R] [Semiring S] [Module R M] [Module S M]
  [DistribSMul S R] [SMulCommClass R S M] [IsScalarTower S R M] (f : End R M)

theorem invtSubmodule_smul (c : Sˣ) : (c • f).invtSubmodule = f.invtSubmodule := by
  apply le_antisymm ?_ (Module.End.invtSubmodule_le_invtSubmodule_smul f c.1)
  grw [Module.End.invtSubmodule_le_invtSubmodule_smul (c.1 • f) c⁻¹.1]
  simp [smul_smul]

