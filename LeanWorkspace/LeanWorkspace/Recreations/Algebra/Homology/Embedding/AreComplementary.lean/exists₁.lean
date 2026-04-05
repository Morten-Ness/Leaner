import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem exists₁ {i₁ : ι₁} (h : e₁.BoundaryLE i₁) :
    ∃ i₂, ac.Boundary i₁ i₂ := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₂, hi₂⟩ := ComplexShape.Embedding.AreComplementary.exists_i₂ ac (c.next (e₁.f i₁))
    (fun i₁' hi₁' => h₂ i₁' (by simpa only [← hi₁'] using h₁))
  exact ⟨i₂, by simpa only [hi₂] using h₁⟩

