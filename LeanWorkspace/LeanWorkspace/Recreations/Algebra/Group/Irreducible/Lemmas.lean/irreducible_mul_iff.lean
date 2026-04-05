import Mathlib

variable {F M N : Type*}

variable [Monoid M] [Monoid N] {f : F} {x y : M}

theorem irreducible_mul_iff :
    Irreducible (x * y) ↔ Irreducible x ∧ IsUnit y ∨ Irreducible y ∧ IsUnit x := by
  constructor
  · refine fun h => Or.imp (fun h' => ⟨?_, h'⟩) (fun h' => ⟨?_, h'⟩) (h.isUnit_or_isUnit rfl).symm
    · rwa [irreducible_mul_isUnit h'] at h
    · rwa [irreducible_isUnit_mul h'] at h
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · rwa [irreducible_mul_isUnit hb]
    · rwa [irreducible_isUnit_mul ha]

