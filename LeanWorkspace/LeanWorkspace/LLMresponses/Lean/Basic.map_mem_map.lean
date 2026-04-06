import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

variable (f : K →+* L)

theorem map_mem_map (f : K →+* L) {s : Subfield K} {x : K} : f x ∈ s.map f ↔ x ∈ s := by
  constructor
  · rintro ⟨y, hy, hfy⟩
    have : y = x := f.injective hfy
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩
