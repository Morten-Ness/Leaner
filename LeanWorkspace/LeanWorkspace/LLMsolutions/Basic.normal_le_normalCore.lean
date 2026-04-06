FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normal_le_normalCore {H : Subgroup G} {N : Subgroup G} [hN : N.Normal] :
    N ≤ H.normalCore ↔ N ≤ H := by
  constructor
  · intro h
    exact le_trans h H.normalCore_le
  · intro h
    intro n hn
    refine show n ∈ H.normalCore from ?_
    rw [Subgroup.mem_inf]
    constructor
    · exact h hn
    · intro g
      change g * n * g⁻¹ ∈ H
      exact h (hN.conj_mem hn g)
