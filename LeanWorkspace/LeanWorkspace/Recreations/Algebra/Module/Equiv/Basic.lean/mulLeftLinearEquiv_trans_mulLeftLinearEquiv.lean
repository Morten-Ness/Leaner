import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]

variable [SMulCommClass R A A]

theorem mulLeftLinearEquiv_trans_mulLeftLinearEquiv (a b : Aˣ) :
    (a.mulLeftLinearEquiv R A).trans (b.mulLeftLinearEquiv R A) =
      (b * a).mulLeftLinearEquiv R A := map_mul _ _ _ |>.symm

