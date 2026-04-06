FAIL
import Mathlib

variable {M : Type*} {S T : Set M}

variable [Semigroup M] {a b : M}

theorem centralizer_eq_top_iff_subset : Set.centralizer S = Set.univ ↔ S ⊆ Set.center M := by
  constructor
  · intro h s hs
    rw [Set.mem_center_iff]
    have hs' : s ∈ Set.centralizer S := by
      rw [h]
      trivial
    exact hs' hs
  · intro h
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      rw [Set.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_center_iff] at h
      exact h hs x
