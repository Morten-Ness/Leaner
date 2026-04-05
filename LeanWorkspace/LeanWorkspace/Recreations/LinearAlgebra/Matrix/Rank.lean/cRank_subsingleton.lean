import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Semiring R]

theorem cRank_subsingleton [Subsingleton R] (A : Matrix m n R) : A.cRank = 1 := rank_subsingleton _ _

