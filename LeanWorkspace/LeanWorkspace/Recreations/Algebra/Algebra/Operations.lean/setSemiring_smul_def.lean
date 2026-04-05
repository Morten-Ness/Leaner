import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

set_option backward.isDefEq.respectTransparency false in
theorem setSemiring_smul_def (s : SetSemiring A) (P : Submodule R A) :
    s • P = span R (SetSemiring.down (α := A) s) * P :=
  rfl

