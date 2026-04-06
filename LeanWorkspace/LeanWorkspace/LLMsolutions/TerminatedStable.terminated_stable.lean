FAIL
import Mathlib

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

theorem terminated_stable (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.TerminatedAt m := by
  rw [GenContFract.terminatedAt_iff_s_none] at terminatedAt_n ⊢
  by_contra hm
  rw [Option.ne_none_iff_exists] at hm
  rcases hm with ⟨gp, hgp⟩
  exact terminatedAt_n <| g.s.monotone n_le_m hgp
