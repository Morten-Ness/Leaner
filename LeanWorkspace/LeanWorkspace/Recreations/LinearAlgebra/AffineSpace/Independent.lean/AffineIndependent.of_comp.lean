import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

variable {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem AffineIndependent.of_comp {p : ι → P} (f : P →ᵃ[k] P₂) (hai : AffineIndependent k (f ∘ p)) :
    AffineIndependent k p := by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i]
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub] at hai
  exact LinearIndependent.of_comp f.linear hai

