import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [NonUnitalNonAssocSemiring R] {M N P : AddSubmonoid R}

variable {M N P Q : AddSubmonoid R}

theorem mul_sup : M * (N ⊔ P) = M * N ⊔ M * P := AddSubmonoid.addSubmonoid_smul_sup

-- need `zero_smul` and `add_smul` to generalize to `SMul`

