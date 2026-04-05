import Mathlib

variable {R : Type u} {M : Type v}

variable [Semiring R] [AddCommMonoid M] [Nontrivial R] [Module R M]

theorem infinite_basis_le_maximal_linearIndependent {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : #ι ≤ #κ := Cardinal.lift_le.mp (infinite_basis_le_maximal_linearIndependent' b v i m)

