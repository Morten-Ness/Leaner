import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [PartialOrder α]

theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) where
  mp _ := PosMulMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_left a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ hbc }

