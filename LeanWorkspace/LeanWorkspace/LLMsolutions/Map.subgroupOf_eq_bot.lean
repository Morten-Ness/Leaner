FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem subgroupOf_eq_bot {H K : Subgroup G} : H.subgroupOf K = ⊥ ↔ Disjoint H K := by
  constructor
  · intro h
    refine disjoint_iff.2 ?_
    intro x hxH hxK
    have hx : (⟨x, hxK⟩ : K) ∈ H.subgroupOf K := hxH
    rw [h, Subgroup.mem_bot] at hx
    exact Subtype.ext_iff.mp hx
  · intro h
    ext x
    constructor
    · intro hx
      have hx1 : ((x : K) : G) = 1 := by
        exact disjoint_iff.1 h ((x : K) : G) hx x.2
      exact Subtype.ext_iff.mpr hx1
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact (H.subgroupOf K).one_mem
