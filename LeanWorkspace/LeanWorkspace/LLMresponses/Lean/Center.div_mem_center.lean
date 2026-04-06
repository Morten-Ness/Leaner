FAIL
import Mathlib

variable {M : Type*} {S T : Set M}

variable [DivisionMonoid M] {a b : M}

theorem div_mem_center (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) : a / b ∈ Set.center M := by
  rw [Set.mem_center_iff] at ha hb ⊢
  exact ha.div hb
