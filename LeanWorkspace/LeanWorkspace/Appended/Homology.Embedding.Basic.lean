import Mathlib

section

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (e : Embedding c c')

theorem f_eq_of_r_eq_some {i : ι} {i' : ι'} (hi : e.r i' = some i) :
    e.f i = i' := by
  by_cases h : ∃ (k : ι), e.f k = i'
  · obtain ⟨k, rfl⟩ := h
    rw [r_f] at hi
    congr 1
    simpa using hi.symm
  · simp [ComplexShape.Embedding.r_eq_none e i' (by simpa using h)] at hi

end

section

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (p : ℤ)

theorem notMem_range_embeddingUpIntGE_iff (n : ℤ) :
    (∀ (i : ℕ), (ComplexShape.embeddingUpIntGE p).f i ≠ n) ↔ n < p := by
  constructor
  · intro h
    by_contra
    exact h (n - p).natAbs (by simp; lia)
  · intros
    dsimp
    lia

end

section

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (p : ℤ)

theorem notMem_range_embeddingUpIntLE_iff (n : ℤ) :
    (∀ (i : ℕ), (ComplexShape.embeddingUpIntLE p).f i ≠ n) ↔ p < n := by
  constructor
  · intro h
    by_contra
    exact h (p - n).natAbs (by simp; lia)
  · intros
    dsimp
    lia

end

section

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (e : Embedding c c')

theorem r_eq_none (i' : ι') (hi : ∀ i, e.f i ≠ i') :
    e.r i' = none := dif_neg (by
    rintro ⟨i, hi'⟩
    exact hi i hi')

end

section

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (e : Embedding c c')

theorem r_eq_some {i : ι} {i' : ι'} (hi : e.f i = i') :
    e.r i' = some i := by
  have h : ∃ (i : ι), e.f i = i' := ⟨i, hi⟩
  have : h.choose = i := e.injective_f (h.choose_spec.trans (hi.symm))
  dsimp [ComplexShape.Embedding.r]
  rw [dif_pos ⟨i, hi⟩, this]

end

section

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (e : Embedding c c')

theorem rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Rel (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂ := by
  constructor
  · apply IsRelIff.rel'
  · exact e.rel

end
