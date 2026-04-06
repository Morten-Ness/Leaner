FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem inf_subgroupOf_inf_normal_of_right (A B' B : Subgroup G)
    [hN : (B'.subgroupOf B).Normal] : ((A ⊓ B').subgroupOf (A ⊓ B)).Normal := by
  rw [Subgroup.normal_iff]
  intro a n
  rcases a with ⟨a, haA, haB⟩
  rcases n with ⟨n, hnAB', hnAB⟩
  change a * n * a⁻¹ ∈ (A ⊓ B').subgroupOf (A ⊓ B)
  change a * n * a⁻¹ ∈ A ⊓ B'
  constructor
  · exact A.mul_mem (A.mul_mem haA hnAB'.1) (A.inv_mem haA)
  · have haB : a ∈ B := haB
    have hnB' : n ∈ B' := hnAB'.2
    have hn_sub : (⟨n, hnB'⟩ : B'.subgroupOf B) ∈ (B'.subgroupOf B) := by
      exact Subgroup.mem_carrier _ _
    have hconj :
        (⟨a * n * a⁻¹,
          by
            refine B.mul_mem (B.mul_mem haB ?_) (B.inv_mem haB)
            exact show n ∈ B from hnAB.2⟩ : B'.subgroupOf B) ∈ (B'.subgroupOf B) := by
      simpa [Subgroup.normal_iff] using
        (show (⟨a, haB⟩ : B) * (⟨n, hnB'⟩ : B'.subgroupOf B) * (⟨a, haB⟩ : B)⁻¹ ∈ (B'.subgroupOf B) from
          (Subgroup.normal_iff.mp hN ⟨a, haB⟩ ⟨n, hnB'⟩ hn_sub))
    exact hconj
