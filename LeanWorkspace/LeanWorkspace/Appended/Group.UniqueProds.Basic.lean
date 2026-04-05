import Mathlib

section

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem exists_iff_exists_existsUnique :
    (∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ UniqueMul A B a0 b0) ↔
      ∃ g : G, ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = g := ⟨fun ⟨_, _, hA, hB, h⟩ ↦ ⟨_, (UniqueMul.iff_existsUnique hA hB).mp h⟩, fun ⟨g, h⟩ ↦ by
    have h' := h
    rcases h' with ⟨⟨a, b⟩, ⟨hab, rfl, -⟩, -⟩
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨a, b, ha, hb, (UniqueMul.iff_existsUnique ha hb).mpr h⟩⟩

end

section

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem iff_existsUnique (aA : a0 ∈ A) (bB : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = a0 * b0 := ⟨fun _ ↦ ⟨(a0, b0), ⟨Finset.mk_mem_product aA bB, rfl⟩, by simpa⟩,
    fun h ↦ h.elim
      (by
        rintro ⟨x1, x2⟩ _ J x y hx hy l
        rcases Prod.mk_inj.mp (J (a0, b0) ⟨Finset.mk_mem_product aA bB, rfl⟩) with ⟨rfl, rfl⟩
        exact Prod.mk_inj.mp (J (x, y) ⟨Finset.mk_mem_product hx hy, l⟩))⟩

end

section

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem mono {A' B' : Finset G} (hA : A ⊆ A') (hB : B ⊆ B') (h : UniqueMul A' B' a0 b0) :
    UniqueMul A B a0 b0 := fun _ _ ha hb he ↦ h (hA ha) (hB hb) he

end

section

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem mulHom_map_iff (f : G ↪ H) (mul : ∀ x y, f (x * y) = f x * f y) :
    UniqueMul (A.map f) (B.map f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := by
  classical simp_rw [← UniqueMul.mulHom_image_iff ⟨f, mul⟩ f.2, Finset.map_eq_image]; rfl

end

section

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem mulHom_preimage (f : G →ₙ* H) (hf : Function.Injective f) (a0 b0 : G) {A B : Finset H}
    (u : UniqueMul A B (f a0) (f b0)) :
    UniqueMul (A.preimage f hf.injOn) (B.preimage f hf.injOn) a0 b0 := by
  intro a b ha hb ab
  simp only [← hf.eq_iff, map_mul] at ab ⊢
  exact u (Finset.mem_preimage.mp ha) (Finset.mem_preimage.mp hb) ab

end

section

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem of_subsingleton [Subsingleton G] : UniqueMul A B a0 b0 := by
  simp [UniqueMul, eq_iff_true_of_subsingleton]

end

section

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem set_subsingleton (h : UniqueMul A B a0 b0) :
    Set.Subsingleton { ab : G × G | ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } := by
  rintro ⟨x1, y1⟩ (hx : x1 ∈ A ∧ y1 ∈ B ∧ x1 * y1 = a0 * b0) ⟨x2, y2⟩
    (hy : x2 ∈ A ∧ y2 ∈ B ∧ x2 * y2 = a0 * b0)
  rcases h hx.1 hx.2.1 hx.2.2 with ⟨rfl, rfl⟩
  rcases h hy.1 hy.2.1 hy.2.2 with ⟨rfl, rfl⟩
  rfl

end

section

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem subsingleton (h : UniqueMul A B a0 b0) :
    Subsingleton { ab : G × G // ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } := ⟨fun ⟨⟨_a, _b⟩, ha, hb, ab⟩ ⟨⟨_a', _b'⟩, ha', hb', ab'⟩ ↦
    Subtype.ext <|
      Prod.ext ((h ha hb ab).1.trans (h ha' hb' ab').1.symm) <|
        (h ha hb ab).2.trans (h ha' hb' ab').2.symm⟩

end
