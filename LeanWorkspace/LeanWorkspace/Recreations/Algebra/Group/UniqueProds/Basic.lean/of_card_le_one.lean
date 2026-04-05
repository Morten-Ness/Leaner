import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem of_card_le_one (hA : A.Nonempty) (hB : B.Nonempty) (hA1 : #A ≤ 1) (hB1 : #B ≤ 1) :
    ∃ a ∈ A, ∃ b ∈ B, UniqueMul A B a b := by
  rw [Finset.card_le_one_iff] at hA1 hB1
  obtain ⟨a, ha⟩ := hA; obtain ⟨b, hb⟩ := hB
  exact ⟨a, ha, b, hb, fun _ _ ha' hb' _ ↦ ⟨hA1 ha' ha, hB1 hb' hb⟩⟩

