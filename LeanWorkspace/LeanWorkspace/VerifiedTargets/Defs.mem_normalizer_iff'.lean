import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem mem_normalizer_iff' {g : G} : g ∈ Subgroup.normalizer H ↔ ∀ n, n * g ∈ H ↔ g * n ∈ H := ⟨fun h n ↦ by rw [← SetLike.mem_coe, ← SetLike.mem_coe, h, mul_assoc, mul_inv_cancel_right],
    fun h n ↦ by rw [SetLike.mem_coe, SetLike.mem_coe, mul_assoc, ← h, inv_mul_cancel_right]⟩

