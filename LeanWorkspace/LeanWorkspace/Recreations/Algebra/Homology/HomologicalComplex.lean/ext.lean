import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {c : ComplexShape ι}

theorem ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.X = C₂.X)
    (h_d :
      ∀ i j : ι,
        c.Rel i j → C₁.d i j ≫ eqToHom (congr_fun h_X j) = eqToHom (congr_fun h_X i) ≫ C₂.d i j) :
    C₁ = C₂ := by
  obtain ⟨X₁, d₁, s₁, h₁⟩ := C₁
  obtain ⟨X₂, d₂, s₂, h₂⟩ := C₂
  dsimp at h_X
  subst h_X
  simp only [HomologicalComplex.mk.injEq, heq_eq_eq, true_and]
  ext i j
  by_cases hij : c.Rel i j
  · simpa only [comp_id, id_comp, eqToHom_refl] using h_d i j hij
  · rw [s₁ i j hij, s₂ i j hij]

