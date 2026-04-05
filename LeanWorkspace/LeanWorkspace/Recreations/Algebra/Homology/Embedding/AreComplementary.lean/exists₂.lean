import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem exists₂ {i₂ : ι₂} (h : e₂.BoundaryGE i₂) :
    ∃ i₁, ac.Boundary i₁ i₂ := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨i₁, hi₁⟩ := ComplexShape.Embedding.AreComplementary.exists_i₁ ac (c.prev (e₂.f i₂))
    (fun i₂' hi₂' => h₂ i₂' (by simpa only [← hi₂'] using h₁))
  exact ⟨i₁, by simpa only [hi₁] using h₁⟩

