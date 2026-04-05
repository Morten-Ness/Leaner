import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem iff_existsUnique (aA : a0 ∈ A) (bB : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = a0 * b0 := ⟨fun _ ↦ ⟨(a0, b0), ⟨Finset.mk_mem_product aA bB, rfl⟩, by simpa⟩,
    fun h ↦ h.elim
      (by
        rintro ⟨x1, x2⟩ _ J x y hx hy l
        rcases Prod.mk_inj.mp (J (a0, b0) ⟨Finset.mk_mem_product aA bB, rfl⟩) with ⟨rfl, rfl⟩
        exact Prod.mk_inj.mp (J (x, y) ⟨Finset.mk_mem_product hx hy, l⟩))⟩

