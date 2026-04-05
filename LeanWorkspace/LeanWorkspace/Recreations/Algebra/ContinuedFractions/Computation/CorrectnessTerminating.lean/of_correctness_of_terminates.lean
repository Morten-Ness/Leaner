import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

variable [FloorRing K]

theorem of_correctness_of_terminates (terminates : (of v).Terminates) :
    ∃ n : ℕ, v = (of v).convs n := Exists.elim terminates fun n terminatedAt_n =>
    Exists.intro n (GenContFract.of_correctness_of_terminatedAt terminatedAt_n)

