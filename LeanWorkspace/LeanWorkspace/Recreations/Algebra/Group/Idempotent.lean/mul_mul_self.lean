import Mathlib

variable {M N S : Type*}

theorem mul_mul_self {M : Type*} [Semigroup M] {x : M}
    (hx : IsIdempotentElem x) (y : M) : y * x * x = y * x := mul_assoc y x x ▸ congrArg (y * ·) IsIdempotentElem.eq hx

