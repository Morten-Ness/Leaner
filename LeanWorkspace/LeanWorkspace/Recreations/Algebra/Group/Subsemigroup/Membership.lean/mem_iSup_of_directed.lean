import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_iSup_of_directed {S : ι → Subsemigroup M} (hS : Directed (· ≤ ·) S) {x : M} :
    (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  have : iSup S = ⨆ i : PLift ι, ⨆ (_ : True), S i.down := by simp [iSup_plift_down]
  rw [this, Subsemigroup.mem_biSup_of_directedOn]
  · simp
  · simp only [setOf_true]
    rw [directedOn_onFun_iff, Set.image_univ, ← directedOn_range]
    -- `Directed.mono_comp` and much of the Set API requires `Type u` instead of `Sort u`
    intro i
    simp only [PLift.exists]
    intro j
    refine (hS i.down j.down).imp ?_
    simp

