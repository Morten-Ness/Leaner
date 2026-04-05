import Mathlib

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

variable (R M) (ι : Type*) [DecidableEq ι]

theorem finsuppLEquivDirectSum_symm_lof (i : ι) (m : M) :
    (finsuppLEquivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsupp.single i m := letI : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  DFinsupp.toFinsupp_single i m

