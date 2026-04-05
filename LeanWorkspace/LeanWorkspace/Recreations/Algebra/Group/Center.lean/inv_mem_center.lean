import Mathlib

variable {M : Type*} {S T : Set M}

variable [DivisionMonoid M] {a b : M}

theorem inv_mem_center (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  rw [Set.mem_center_iff _root_.Semigroup]
  intro _
  rw [← inv_inj, mul_inv_rev, inv_inv, ha.comm, mul_inv_rev, inv_inv]

