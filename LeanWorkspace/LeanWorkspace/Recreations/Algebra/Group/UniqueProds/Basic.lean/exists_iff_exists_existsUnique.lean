import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem exists_iff_exists_existsUnique :
    (∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ UniqueMul A B a0 b0) ↔
      ∃ g : G, ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = g := ⟨fun ⟨_, _, hA, hB, h⟩ ↦ ⟨_, (UniqueMul.iff_existsUnique hA hB).mp h⟩, fun ⟨g, h⟩ ↦ by
    have h' := h
    rcases h' with ⟨⟨a, b⟩, ⟨hab, rfl, -⟩, -⟩
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨a, b, ha, hb, (UniqueMul.iff_existsUnique ha hb).mpr h⟩⟩

