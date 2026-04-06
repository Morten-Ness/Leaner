FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem vectorSpan_eq_top_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) :
    vectorSpan k s = ⊤ := by
  by_cases hs : s.Nonempty
  · rcases hs with ⟨p, hp⟩
    rw [← AffineSubspace.direction_eq_top_iff_of_nonempty (p := p)]
    · rw [affineSpan_direction]
      simpa [h]
    · exact subset_affineSpan k s hp
  · have hs' : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    simp at h
