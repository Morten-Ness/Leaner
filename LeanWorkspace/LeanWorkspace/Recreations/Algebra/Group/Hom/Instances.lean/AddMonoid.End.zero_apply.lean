import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem AddMonoid.End.zero_apply [AddCommMonoid M] (m : M) : (0 : AddMonoid.End M) m = 0 := rfl

-- Note: `@[simp]` omitted because `(1 : AddMonoid.End M) = id` by `AddMonoid.End.coe_one`

