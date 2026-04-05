import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem zero_le_of_contsAux_b : 0 ≤ ((of v).contsAux n).b := by
  let g := of v
  induction n with
  | zero => rfl
  | succ n IH =>
    rcases Decidable.em <| g.TerminatedAt (n - 1) with terminated | not_terminated
    · -- terminating case
      rcases n with - | n
      · simp [zero_le_one]
      · have : g.contsAux (n + 2) = g.contsAux (n + 1) :=
          contsAux_stable_step_of_terminated terminated
        simp only [g, this, IH]
    · -- non-terminating case
      calc
        (0 : K) ≤ fib (n + 1) := mod_cast (n + 1).fib.zero_le
        _ ≤ ((of v).contsAux (n + 1)).b := GenContFract.fib_le_of_contsAux_b (Or.inr not_terminated)

