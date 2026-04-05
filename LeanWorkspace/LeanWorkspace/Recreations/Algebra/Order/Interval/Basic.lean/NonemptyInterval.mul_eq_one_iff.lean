import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s t : NonemptyInterval α}

theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = pure a ∧ t = pure b ∧ a * b = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [NonemptyInterval.ext_iff, Prod.ext_iff] at h
    have := (mul_le_mul_iff_of_ge s.fst_le_snd t.fst_le_snd).1 (h.2.trans h.1.symm).le
    refine ⟨s.fst, t.fst, ?_, ?_, h.1⟩ <;> apply NonemptyInterval.ext <;> dsimp [pure]
    · nth_rw 2 [this.1]
    · nth_rw 2 [this.2]
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [NonemptyInterval.pure_mul_pure, h, NonemptyInterval.pure_one]

