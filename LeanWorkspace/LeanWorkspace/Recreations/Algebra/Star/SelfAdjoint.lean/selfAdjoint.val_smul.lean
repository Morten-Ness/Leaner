import Mathlib

variable {R A : Type*}

variable [Star R] [TrivialStar R] [AddGroup A] [StarAddMonoid A]

theorem val_smul [SMul R A] [StarModule R A] (r : R) (x : selfAdjoint A) : ↑(r • x) = r • (x : A) := rfl

