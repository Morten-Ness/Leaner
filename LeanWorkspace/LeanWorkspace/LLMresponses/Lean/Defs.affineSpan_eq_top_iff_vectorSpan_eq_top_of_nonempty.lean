FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty {s : Set P} (hs : s.Nonempty) :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  rcases hs with ⟨p, hp⟩
  constructor
  · intro h
    rw [← top_le_iff, ← h]
    exact AffineSubspace.direction_le_vectorSpan k s
  · intro h
    rw [← top_le_iff]
    intro q hq
    rw [show q = p +ᵥ (q -ᵥ p) by simpa using (vadd_vsub q p)]
    refine AffineSubspace.vadd_mem_of_mem_direction ?_ ?_
    · exact AffineSubspace.subset_affineSpan k hp
    · rw [h]
      exact Submodule.mem_top
