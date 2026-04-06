FAIL
import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem centralizer_centralizer_comm_of_comm (h_comm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ S.centralizer.centralizer, ∀ y ∈ S.centralizer.centralizer, x * y = y * x := by
  intro x hx y hy
  rw [Set.mem_centralizer_iff] at hx hy
  exact hx y <| by
    rw [Set.mem_centralizer_iff]
    intro z hz
    exact h_comm y (by
      rw [Set.mem_centralizer_iff] at hy
      exact hy z hz) z hz
