FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial {s : Set P} [Nontrivial P] :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  classical
  by_cases hs : s.Nonempty
  · rcases hs with ⟨p, hp⟩
    simpa using
      AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty (k := k) (s := s) p hp
  · have hs' : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    have hP : (Set.univ : Set P).Nonempty := Set.univ_nonempty
    rw [affineSpan_empty, vectorSpan_empty]
    simp [hP]
