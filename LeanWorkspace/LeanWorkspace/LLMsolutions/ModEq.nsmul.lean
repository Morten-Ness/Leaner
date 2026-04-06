FAIL
import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem nsmul {n : ℕ} (h : a ≡ b [PMOD p]) : n • a ≡ n • b [PMOD n • p] := by
  rcases h with ⟨k, hk⟩
  rcases hk with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  calc
    m • (n • p) + n • a = n • (m • p + a) := by
      simp [nsmul_add, add_comm, add_left_comm, add_assoc]
    _ = n • (k • p + b) := by rw [hm]
    _ = k • (n • p) + n • b := by
      simp [nsmul_add, add_comm, add_left_comm, add_assoc]
