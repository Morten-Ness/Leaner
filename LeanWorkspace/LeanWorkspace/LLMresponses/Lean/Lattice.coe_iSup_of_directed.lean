FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem coe_iSup_of_directed {ι} [Nonempty ι] {S : ι → Subgroup G} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subgroup G) : Set G) = ⋃ i, S i := by
  ext x
  simp only [Set.mem_iUnion]
  exact Subgroup.mem_iSup_of_directed hS x
