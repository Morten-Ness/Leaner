import Mathlib

variable {R n : Type*}

variable [NonUnitalNonAssocSemiring R] [Fintype n]

theorem matrix_strictMono_of_nonempty [Nonempty n] :
    StrictMono (RingCon.matrix (R := R) n) :=
  RingCon.matrix_monotone n |>.strictMono_of_injective <| RingCon.matrix_injective _

