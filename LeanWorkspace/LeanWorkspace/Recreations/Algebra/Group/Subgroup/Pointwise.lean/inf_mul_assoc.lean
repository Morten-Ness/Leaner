import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem inf_mul_assoc (A B C : Subgroup G) (h : C ≤ A) :
    ((A ⊓ B : Subgroup G) : Set G) * C = (A : Set G) ∩ (↑B * ↑C) := by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, z, hz, rfl⟩
    refine ⟨A.mul_mem hyA (h hz), ?_⟩
    exact ⟨y, hyB, z, hz, rfl⟩
  rintro ⟨hyz, y, hy, z, hz, rfl⟩
  refine ⟨y, ⟨?_, hy⟩, z, hz, rfl⟩
  suffices y * z * z⁻¹ ∈ A by simpa
  exact mul_mem hyz (inv_mem (h hz))

