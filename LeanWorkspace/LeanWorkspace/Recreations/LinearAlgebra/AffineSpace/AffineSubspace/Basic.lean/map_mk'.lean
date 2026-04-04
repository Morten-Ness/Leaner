import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem map_mk' (p : P₁) (direction : Submodule k V₁) :
    (mk' p direction).map f = mk' (f p) (direction.map f.linear) := by
  ext q
  simp only [AffineSubspace.mem_map, mem_mk', Submodule.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r -ᵥ p, hr, by simp⟩
  · rintro ⟨r, hr, he⟩
    exact ⟨r +ᵥ p, by simp [hr], by simp [he]⟩

