import Mathlib

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

variable (R M) (ι : Type*) [DecidableEq ι]

theorem finsuppLEquivDirectSum_single (i : ι) (m : M) :
    finsuppLEquivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i m := Finsupp.toDFinsupp_single i m

