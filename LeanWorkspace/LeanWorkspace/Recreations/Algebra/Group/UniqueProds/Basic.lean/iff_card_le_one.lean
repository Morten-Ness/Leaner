import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem iff_card_le_one [DecidableEq G] (ha0 : a0 ∈ A) (hb0 : b0 ∈ B) :
    UniqueMul A B a0 b0 ↔ #{p ∈ A ×ˢ B | p.1 * p.2 = a0 * b0} ≤ 1 := by
  simp_rw [card_le_one_iff, mem_filter, mem_product]
  refine ⟨fun h p1 p2 ⟨⟨ha1, hb1⟩, he1⟩ ⟨⟨ha2, hb2⟩, he2⟩ ↦ ?_, fun h a b ha hb he ↦ ?_⟩
  · have h1 := h ha1 hb1 he1; have h2 := h ha2 hb2 he2
    grind
  · exact Prod.ext_iff.1 (@h (a, b) (a0, b0) ⟨⟨ha, hb⟩, he⟩ ⟨⟨ha0, hb0⟩, rfl⟩)

