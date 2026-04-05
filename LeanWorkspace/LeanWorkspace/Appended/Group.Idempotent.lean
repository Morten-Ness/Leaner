import Mathlib

section

variable {M N S : Type*}

theorem map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M}
    (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e) := by
  rw [IsIdempotentElem, ← map_mul, IsIdempotentElem.eq he]

end

section

variable {M N S : Type*}

variable [Semigroup S] {a b : S}

theorem mul_of_commute (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a * b) := by rw [IsIdempotentElem, hab.symm.mul_mul_mul_comm, IsIdempotentElem.eq ha, IsIdempotentElem.eq hb]

end

section

variable {M N S : Type*}

variable [Mul M] {a : M}

theorem of_isIdempotent [Std.IdempotentOp (α := M) (· * ·)] (a : M) : IsIdempotentElem a :=
  Std.IdempotentOp.idempotent a

end

section

variable {M N S : Type*}

variable [Monoid M] {a : M}

theorem pow_succ_eq (n : ℕ) (h : IsIdempotentElem a) : a ^ (n + 1) = a := Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one a) fun n ih => by rw [pow_succ, ih, IsIdempotentElem.eq h]

end
