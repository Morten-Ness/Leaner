import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

variable [FloorRing K]

theorem of_correctness_atTop_of_terminates (terminates : (of v).Terminates) :
    ∀ᶠ n in atTop, v = (of v).convs n := by
  rw [eventually_atTop]
  obtain ⟨n, terminatedAt_n⟩ : ∃ n, (of v).TerminatedAt n := terminates
  use n
  intro m m_geq_n
  rw [convs_stable_of_terminated m_geq_n terminatedAt_n]
  exact GenContFract.of_correctness_of_terminatedAt terminatedAt_n

