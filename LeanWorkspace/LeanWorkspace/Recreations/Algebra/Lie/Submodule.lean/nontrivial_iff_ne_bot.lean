import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem nontrivial_iff_ne_bot {N : LieSubmodule R L M} : Nontrivial N ↔ N ≠ ⊥ := by
  constructor
  · rintro ⟨⟨m₁, h₁⟩, ⟨m₂, h₂⟩, h₁₂⟩ rfl
    simp [(LieSubmodule.mem_bot _).mp h₁, (LieSubmodule.mem_bot _).mp h₂] at h₁₂
  · contrapose!
    rw [LieSubmodule.eq_bot_iff]
    rintro ⟨h⟩ m hm
    simpa using h ⟨m, hm⟩ ⟨_, N.zero_mem⟩

