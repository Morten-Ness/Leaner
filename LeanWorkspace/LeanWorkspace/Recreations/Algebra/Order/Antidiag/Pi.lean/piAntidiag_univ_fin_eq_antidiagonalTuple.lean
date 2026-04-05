import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι]

theorem piAntidiag_univ_fin_eq_antidiagonalTuple (n k : ℕ) :
    Finset.piAntidiag univ n = Nat.antidiagonalTuple k n := by
  ext; simp [Nat.mem_antidiagonalTuple]

