import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mem_direction_iff_eq_vsub {s : AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V) :
    v ∈ s.direction ↔ ∃ p₁ ∈ s, ∃ p₂ ∈ s, v = p₁ -ᵥ p₂ := by
  rcases h with ⟨p, hp⟩
  constructor
  · intro hv
    refine ⟨v +ᵥ p, s.vadd_mem_of_mem_direction hv hp, p, hp, ?_⟩
    simp
  · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    exact s.vsub_mem_direction hp₁ hp₂
