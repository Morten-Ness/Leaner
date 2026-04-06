import Mathlib

variable {K : Type*} [Field K] {s : SimpContFract K} {n : ℕ}

theorem determinant (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n) :
    (↑s : GenContFract K).nums n * (↑s : GenContFract K).dens (n + 1) -
      (↑s : GenContFract K).dens n * (↑s : GenContFract K).nums (n + 1) = (-1) ^ (n + 1) := by
  simpa using SimpContFract.determinant (s := s) not_terminatedAt_n
