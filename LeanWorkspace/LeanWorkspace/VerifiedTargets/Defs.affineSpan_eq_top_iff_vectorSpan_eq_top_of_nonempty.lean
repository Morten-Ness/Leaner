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
  refine ⟨AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top k V P, ?_⟩
  intro h
  suffices Nonempty (affineSpan k s) by
    obtain ⟨p, hp : p ∈ affineSpan k s⟩ := this
    rw [AffineSubspace.eq_iff_direction_eq_of_mem hp (AffineSubspace.mem_top k V p), direction_affineSpan, h, AffineSubspace.direction_top]
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨x, mem_affineSpan k hx⟩⟩

