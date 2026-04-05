import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_sSup_of_directedOn {K : Set (Subgroup G)} (Kne : K.Nonempty) (hK : DirectedOn (· ≤ ·) K)
    {x : G} : x ∈ sSup K ↔ ∃ s ∈ K, x ∈ s := by
  haveI : Nonempty K := Kne.to_subtype
  simp only [sSup_eq_iSup', Subgroup.mem_iSup_of_directed hK.directed_val, SetCoe.exists, exists_prop]

