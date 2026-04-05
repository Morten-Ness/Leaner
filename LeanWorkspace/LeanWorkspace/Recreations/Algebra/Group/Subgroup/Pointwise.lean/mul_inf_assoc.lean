import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem mul_inf_assoc (A B C : Subgroup G) (h : A ≤ C) :
    (A : Set G) * ↑(B ⊓ C) = (A : Set G) * (B : Set G) ∩ C := by
  ext
  simp only [coe_inf, Set.mem_mul, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, z, ⟨hzB, hzC⟩, rfl⟩
    refine ⟨?_, mul_mem (h hy) hzC⟩
    exact ⟨y, hy, z, hzB, rfl⟩
  rintro ⟨⟨y, hy, z, hz, rfl⟩, hyz⟩
  refine ⟨y, hy, z, ⟨hz, ?_⟩, rfl⟩
  suffices y⁻¹ * (y * z) ∈ C by simpa
  exact mul_mem (inv_mem (h hy)) hyz

