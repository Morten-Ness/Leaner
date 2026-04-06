import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem le_normalizer : H ≤ Subgroup.normalizer H := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact H.mul_mem (H.mul_mem hh hn) (H.inv_mem hh)
  · intro hn
    have h_inv : h⁻¹ ∈ H := H.inv_mem hh
    have : h⁻¹ * (h * n * h⁻¹) * h ∈ H := H.mul_mem (H.mul_mem h_inv hn) hh
    simpa [mul_assoc] using this
