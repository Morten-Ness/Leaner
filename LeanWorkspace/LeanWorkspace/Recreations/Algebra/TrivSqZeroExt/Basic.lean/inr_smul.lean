import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inr_smul [Zero R] [SMulZeroClass S R] [SMul S M] (r : S) (m : M) :
    (TrivSqZeroExt.inr (r • m) : tsze R M) = r • TrivSqZeroExt.inr m := TrivSqZeroExt.ext (smul_zero _).symm rfl

