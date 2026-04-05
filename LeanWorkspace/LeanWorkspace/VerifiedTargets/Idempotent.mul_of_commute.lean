import Mathlib

variable {M N S : Type*}

variable [Semigroup S] {a b : S}

theorem mul_of_commute (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a * b) := by rw [IsIdempotentElem, hab.symm.mul_mul_mul_comm, IsIdempotentElem.eq ha, IsIdempotentElem.eq hb]

