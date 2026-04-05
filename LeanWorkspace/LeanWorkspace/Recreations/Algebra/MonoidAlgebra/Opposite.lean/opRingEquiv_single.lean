import Mathlib

variable {R M : Type*} [Semiring R] [Mul M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem opRingEquiv_single (r : R) (x : M) :
    MonoidAlgebra.opRingEquiv (op (single x r)) = single (op x) (op r) := by simp

