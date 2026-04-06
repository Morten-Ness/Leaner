FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem normal_subgroupOf_iff {H K : Subgroup G} (hHK : H ≤ K) :
    (H.subgroupOf K).Normal ↔ ∀ h k, h ∈ H → k ∈ K → k * h * k⁻¹ ∈ H := by
  constructor
  · intro hnormal h k hh hk
    have hh' : (⟨h, hHK hh⟩ : K) ∈ H.subgroupOf K := hh
    simpa using hnormal.conj_mem hh' (⟨k, hk⟩ : K)
  · intro h
    constructor
    intro n hn g
    change ((g : G) * (n : G) * (g : G)⁻¹) ∈ H
    exact h n g hn g.property
