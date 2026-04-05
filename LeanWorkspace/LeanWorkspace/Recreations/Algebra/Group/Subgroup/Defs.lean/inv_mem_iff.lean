import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

theorem inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvMemClass S G] {H : S}
    {x : G} : x⁻¹ ∈ H ↔ x ∈ H := ⟨fun h => inv_inv x ▸ inv_mem h, inv_mem⟩

