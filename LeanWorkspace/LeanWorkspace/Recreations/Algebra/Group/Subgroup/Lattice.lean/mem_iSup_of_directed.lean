import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {K : ι → Subgroup G} (hK : Directed (· ≤ ·) K)
    {x : G} : x ∈ (iSup K : Subgroup G) ↔ ∃ i, x ∈ K i := by
  have : iSup K = ⨆ i : PLift ι, ⨆ (_ : True), K i.down := by simp [iSup_plift_down]
  rw [this, Subgroup.mem_biSup_of_directedOn trivial]
  · simp
  · simp only [setOf_true]
    rw [directedOn_onFun_iff, Set.image_univ, ← directedOn_range]
    -- `Directed.mono_comp` and much of the Set API requires `Type u` instead of `Sort u`
    intro i
    simp only [PLift.exists]
    intro j
    refine (hK i.down j.down).imp ?_
    simp
  · exact PLift.up hι.some

