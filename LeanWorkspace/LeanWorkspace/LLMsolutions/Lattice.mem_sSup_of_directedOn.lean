import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_sSup_of_directedOn {K : Set (Subgroup G)} (Kne : K.Nonempty) (hK : DirectedOn (· ≤ ·) K)
    {x : G} : x ∈ sSup K ↔ ∃ s ∈ K, x ∈ s := by
  classical
  constructor
  · intro hx
    rw [Subgroup.mem_sSup_of_directedOn Kne hK] at hx
    simpa using hx
  · rintro ⟨s, hsK, hxs⟩
    rw [Subgroup.mem_sSup_of_directedOn Kne hK]
    exact ⟨s, hsK, hxs⟩
