FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem inf_subgroupOf_inf_normal_of_left {A' A : Subgroup G} (B : Subgroup G)
    [hN : (A'.subgroupOf A).Normal] : ((A' ⊓ B).subgroupOf (A ⊓ B)).Normal := by
  classical
  let f : A ⊓ B →* A.subgroupOf A := (A ⊓ B).subgroupOf A
  let K : Subgroup (A ⊓ B) := ((A' ⊓ B).subgroupOf (A ⊓ B))
  have hker : K = f.ker := by
    ext x
    constructor
    · intro hx
      change ((x : A ⊓ B) : G) ∈ A' ⊓ B at hx ⊢
      exact hx
    · intro hx
      change f x = 1 at hx
      change ((x : A ⊓ B) : G) ∈ A' ⊓ B
      have hx' : ((x : A ⊓ B) : G) ∈ A' := by
        have : ((f x : A) : G) = 1 := congrArg Subtype.val hx
        change ((x : A ⊓ B) : G) = 1 at this
        simpa [this]
      exact ⟨hx', (x : A ⊓ B).property.2⟩
  rw [hker]
  infer_instance
