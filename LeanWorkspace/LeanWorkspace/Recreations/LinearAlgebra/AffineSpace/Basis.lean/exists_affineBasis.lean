import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

variable (k V P)

theorem exists_affineBasis : ∃ (s : Set P) (b : AffineBasis (↥s) k P), ⇑b = ((↑) : s → P) := let ⟨s, _, hs⟩ := AffineBasis.exists_affine_subbasis (AffineSubspace.span_univ k V P)
  ⟨s, hs⟩

