import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S)
    {x : M} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  have : iSup S = ⨆ i : PLift ι, ⨆ (_ : True), S i.down := by simp [iSup_plift_down]
  rw [this, Submonoid.mem_biSup_of_directedOn trivial]
  · simp
  · simp only [setOf_true]
    rw [directedOn_onFun_iff, Set.image_univ, ← directedOn_range]
    -- `Directed.mono_comp` and much of the Set API requires `Type u` instead of `Sort u`
    intro i
    simp only [PLift.exists]
    intro j
    refine (hS i.down j.down).imp ?_
    simp
  · exact PLift.up hι.some

