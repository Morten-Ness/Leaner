FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

theorem affineSpan_eq_sInf (s : Set P) :
    affineSpan k s = sInf { s' : AffineSubspace k P | s ⊆ s' } := by
  ext p
  constructor
  · intro hp
    rw [AffineSubspace.mem_sInf]
    intro s' hs'
    exact hs' hp
  · intro hp
    rw [affineSpan]
    by_cases hs : s.Nonempty
    · rcases hs with ⟨p0, hp0⟩
      rw [show spanPoints k s = (Submodule.span k ((fun p : P => p -ᵥ p0) '' s)) by
        ext v
        rw [AffineSubspace.mem_spanPoints]
        simp [hp0]]
      have hp' := hp ⟨p0, by
        intro x hx
        rw [AffineSubspace.mem_mk]
        exact Submodule.subset_span ⟨x, hx, rfl⟩⟩
      rw [AffineSubspace.mem_mk] at hp'
      exact hp'
    · have hs' : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
      subst hs'
      simp [AffineSubspace.mem_sInf] at hp ⊢
