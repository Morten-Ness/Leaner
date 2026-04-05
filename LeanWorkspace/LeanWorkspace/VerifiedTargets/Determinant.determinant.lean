import Mathlib

variable {K : Type*} [Field K] {s : SimpContFract K} {n : ℕ}

theorem determinant (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n) :
    (↑s : GenContFract K).nums n * (↑s : GenContFract K).dens (n + 1) -
      (↑s : GenContFract K).dens n * (↑s : GenContFract K).nums (n + 1) = (-1) ^ (n + 1) := SimpContFract.determinant_aux <| Or.inr <| not_terminatedAt_n

