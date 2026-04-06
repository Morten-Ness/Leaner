FAIL
import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem exists_iff_exists_existsUnique :
    (∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ UniqueMul A B a0 b0) ↔
      ∃ g : G, ∃! ab, ab ∈ A ×ˢ B ∧ ab.1 * ab.2 = g := by
  constructor
  · rintro ⟨a0, b0, ha0, hb0, huniq⟩
    refine ⟨a0 * b0, ⟨(a0, b0), ?_, ?_⟩⟩
    · exact ⟨by simp [Finset.mem_product, ha0, hb0], rfl⟩
    · intro ab hab
      rcases hab with ⟨habmem, habeq⟩
      rw [Finset.mem_product] at habmem
      rcases habmem with ⟨ha, hb⟩
      rcases huniq ha hb habeq with ⟨h1, h2⟩
      cases ab
      simp at h1 h2
      simp [h1, h2]
  · rintro ⟨g, ⟨ab0, hab0, huniq⟩⟩
    rcases ab0 with ⟨a0, b0⟩
    rcases hab0 with ⟨habmem, hg⟩
    rw [Finset.mem_product] at habmem
    rcases habmem with ⟨ha0, hb0⟩
    refine ⟨a0, b0, ha0, hb0, ?_⟩
    intro a b ha hb habeq
    have hab : (a, b) ∈ A ×ˢ B ∧ (a, b).1 * (a, b).2 = g := by
      refine ⟨?_, ?_⟩
      · simp [Finset.mem_product, ha, hb]
      · simpa using habeq
    have hEq : (a, b) = (a0, b0) := huniq (a, b) hab
    exact Prod.mk.inj_iff.mp hEq
