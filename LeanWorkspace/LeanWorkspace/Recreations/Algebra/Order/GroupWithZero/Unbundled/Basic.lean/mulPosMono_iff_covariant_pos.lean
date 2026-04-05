import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [PartialOrder α]

theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) where
  mp _ := MulPosMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_right a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ hbc }

