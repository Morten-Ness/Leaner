import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem map_inf (s t : Subfield K) (f : K →+* L) : (s ⊓ t).map f = s.map f ⊓ t.map f := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy_s, hy_t⟩, rfl⟩
    exact ⟨⟨y, hy_s, rfl⟩, ⟨y, hy_t, rfl⟩⟩
  · rintro ⟨⟨y, hy, hxy⟩, ⟨z, hz, hxz⟩⟩
    have h : f y = f z := by simpa [hxy, hxz]
    have hyz : y = z := f.injective h
    subst z
    exact ⟨y, ⟨hy, hz⟩, hxy⟩
