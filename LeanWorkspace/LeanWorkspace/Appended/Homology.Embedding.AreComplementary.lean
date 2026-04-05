import Mathlib

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable {X : ι → Type*} (x₁ : ∀ i₁, X (e₁.f i₁)) (x₂ : ∀ i₂, X (e₂.f i₂))

theorem desc_inl (i₁ : ι₁) : ac.desc x₁ x₂ (e₁.f i₁) = x₁ i₁ := by
  dsimp [ComplexShape.Embedding.AreComplementary.desc]
  rw [ComplexShape.Embedding.AreComplementary.desc'_inl ac _ _ _ i₁ (ac.equiv.injective (by simp)), ComplexShape.Embedding.AreComplementary.desc.aux_trans]
  rfl

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable {X : ι → Type*} (x₁ : ∀ i₁, X (e₁.f i₁)) (x₂ : ∀ i₂, X (e₂.f i₂))

theorem desc_inr (i₂ : ι₂) : ac.desc x₁ x₂ (e₂.f i₂) = x₂ i₂ := by
  dsimp [ComplexShape.Embedding.AreComplementary.desc]
  rw [ComplexShape.Embedding.AreComplementary.desc'_inr ac _ _ _ i₂ (ac.equiv.injective (by simp)), ComplexShape.Embedding.AreComplementary.desc.aux_trans]
  rfl

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

theorem embeddingUpInt_areComplementary (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    AreComplementary (embeddingUpIntLE n₀) (embeddingUpIntGE n₁) where
  disjoint i₁ i₂ := by dsimp; lia
  union i := by
    by_cases hi : i ≤ n₀
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le hi
      exact Or.inl ⟨k, by dsimp; lia⟩
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le (show n₁ ≤ i by lia)
      exact Or.inr ⟨k, rfl⟩

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

theorem exists_i₁ (i : ι) (hi : ∀ i₂, e₂.f i₂ ≠ i) :
    ∃ i₁, i = e₁.f i₁ := by
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · exact ⟨_, rfl⟩
  · exfalso
    exact hi i₂ rfl

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

theorem exists_i₂ (i : ι) (hi : ∀ i₁, e₁.f i₁ ≠ i) :
    ∃ i₂, i = e₂.f i₂ := ComplexShape.Embedding.AreComplementary.exists_i₁ ComplexShape.Embedding.AreComplementary.symm ac i hi

end

section

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

end

section

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

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

theorem fromSum_bijective : Function.Bijective (ComplexShape.Embedding.AreComplementary.fromSum e₁ e₂) := by
  constructor
  · rintro (i₁ | i₂) (j₁ | j₂) h
    · obtain rfl := e₁.injective_f h
      rfl
    · exact (ac.disjoint _ _ h).elim
    · exact (ac.disjoint _ _ ComplexShape.Embedding.AreComplementary.symm h).elim
    · obtain rfl := e₂.injective_f h
      rfl
  · intro n
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union n
    · exact ⟨Sum.inl i₁, rfl⟩
    · exact ⟨Sum.inr i₂, rfl⟩

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

variable {i₁ : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂)

theorem fst : e₁.BoundaryLE i₁ := e₁.boundaryLE h (fun _ => ac.disjoint _ _)

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem hom_ext' (φ : K ⟶ L) (hK : K.IsStrictlySupportedOutside e₂)
    (hL : L.IsStrictlySupportedOutside e₁) :
    φ = 0 := by
  ext i
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · apply (hL.isZero i₁).eq_of_tgt
  · apply (hK.isZero i₂).eq_of_src

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem hom_ext [K.IsStrictlySupported e₁] [L.IsStrictlySupported e₂] (φ : K ⟶ L) :
    φ = 0 := by
  apply ComplexShape.Embedding.AreComplementary.hom_ext' ac
  · rw [ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside₂_iff ac]
    infer_instance
  · rw [ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside₁_iff ac]
    infer_instance

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem isStrictlySupportedOutside₁_iff :
    K.IsStrictlySupportedOutside e₁ ↔ K.IsStrictlySupported e₂ := by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ComplexShape.Embedding.AreComplementary.exists_i₁ ac i hi
      exact h.isZero i₁⟩
  · intro _
    exact ⟨fun i₁ => K.isZero_X_of_isStrictlySupported e₂ _
      (fun i₂ => ComplexShape.Embedding.AreComplementary.symm (ac.disjoint i₁ i₂))⟩

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem isStrictlySupportedOutside₂_iff :
    K.IsStrictlySupportedOutside e₂ ↔ K.IsStrictlySupported e₁ := ComplexShape.Embedding.AreComplementary.isStrictlySupportedOutside₁_iff ComplexShape.Embedding.AreComplementary.symm ac K

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem isSupportedOutside₁_iff :
    K.IsSupportedOutside e₁ ↔ K.IsSupported e₂ := by
  constructor
  · intro h
    exact ⟨fun i hi => by
      obtain ⟨i₁, rfl⟩ := ComplexShape.Embedding.AreComplementary.exists_i₁ ac i hi
      exact h.exactAt i₁⟩
  · intro _
    exact ⟨fun i₁ => K.exactAt_of_isSupported e₂ _
      (fun i₂ => ComplexShape.Embedding.AreComplementary.symm (ac.disjoint i₁ i₂))⟩

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem isSupportedOutside₂_iff :
    K.IsSupportedOutside e₂ ↔ K.IsSupported e₁ := ComplexShape.Embedding.AreComplementary.isSupportedOutside₁_iff ComplexShape.Embedding.AreComplementary.symm ac K

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem of_boundaryGE {i₂ : ι₂} (h : e₂.BoundaryGE i₂) :
    ac.Boundary (ComplexShape.Embedding.AreComplementary.Boundary.indexOfBoundaryGE ac h) i₂ := (ComplexShape.Embedding.AreComplementary.Boundary.exists₂ ac h).choose_spec

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

theorem of_boundaryLE {i₁ : ι₁} (h : e₁.BoundaryLE i₁) :
    ac.Boundary i₁ (ComplexShape.Embedding.AreComplementary.Boundary.indexOfBoundaryLE ac h) := (ComplexShape.Embedding.AreComplementary.Boundary.exists₁ ac h).choose_spec

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable (K L : HomologicalComplex C c)

variable {i₁ : ι₁} {i₂ : ι₂} (h : ac.Boundary i₁ i₂)

theorem snd : e₂.BoundaryGE i₂ := e₂.boundaryGE h (fun _ => ComplexShape.Embedding.AreComplementary.symm ac.disjoint _ _)

end

section

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

theorem symm : ComplexShape.Embedding.AreComplementary e₂ e₁ where
  disjoint i₂ i₁ := (ac.disjoint i₁ i₂).symm
  union i := (ac.union i).symm

end
