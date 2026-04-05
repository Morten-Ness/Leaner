import Mathlib

variable {F α β R S S' : Type*}

theorem isDomain {A : Type*} (B : Type*) [Semiring A] [Semiring B] [IsDomain B]
    (e : A ≃* B) : IsDomain A := { RingEquiv.injective e.isLeftCancelMulZero e (RingEquiv.map_zero e) (RingEquiv.map_mul e),
    RingEquiv.injective e.isRightCancelMulZero e (RingEquiv.map_zero e) (RingEquiv.map_mul e) with
    exists_pair_ne := ⟨e.symm 0, e.symm 1, RingEquiv.injective e.symm.ne zero_ne_one⟩ }

