import Mathlib

variable {R : Type*}

variable {G : Type*} [Group G] [StarMul G]

theorem Unitary.inv_mem {g : G} (hg : g ∈ unitary G) : g⁻¹ ∈ unitary G := by
  simp_rw [Unitary.mem_iff, star_inv, ← mul_inv_rev, inv_eq_one] at *
  exact hg.symm

