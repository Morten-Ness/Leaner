import Mathlib

variable {R A : Type*}

variable [Star R] [TrivialStar R] [AddCommGroup A] [StarAddMonoid A]

theorem val_smul [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) (x : skewAdjoint A) :
    ↑(r • x) = r • (x : A) := rfl

