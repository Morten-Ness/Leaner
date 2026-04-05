import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_inter_nonempty_iff {s t : Set α} {x : α} :
    (x • s ∩ t).Nonempty ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x := by
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩

