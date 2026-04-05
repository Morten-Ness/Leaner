import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Semiring R]

theorem cRank_toNat_eq_finrank (A : Matrix m n R) :
    A.cRank.toNat = Module.finrank R (span R (Set.range A.col)) := rfl

