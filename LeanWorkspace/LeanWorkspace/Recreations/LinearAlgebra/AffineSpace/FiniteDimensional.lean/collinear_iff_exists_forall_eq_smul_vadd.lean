import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

theorem collinear_iff_exists_forall_eq_smul_vadd (s : Set P) :
    Collinear k s ↔ ∃ (p₀ : P) (v : V), ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ := by
  rcases Set.eq_empty_or_nonempty s with (rfl | ⟨⟨p₁, hp₁⟩⟩)
  · simp [collinear_empty]
  · rw [collinear_iff_of_mem hp₁]
    constructor
    · exact fun h => ⟨p₁, h⟩
    · rintro ⟨p, v, hv⟩
      use v
      intro p₂ hp₂
      rcases hv p₂ hp₂ with ⟨r, rfl⟩
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩
      use r - r₁
      simp [vadd_vadd, ← add_smul]

