import Mathlib

variable {M N S : Type*}

theorem mul_self_mul {M : Type*} [Semigroup M] {x : M}
    (hx : IsIdempotentElem x) (y : M) : x * (x * y) = x * y := mul_assoc x x y ▸ congrArg (· * y) IsIdempotentElem.eq hx

