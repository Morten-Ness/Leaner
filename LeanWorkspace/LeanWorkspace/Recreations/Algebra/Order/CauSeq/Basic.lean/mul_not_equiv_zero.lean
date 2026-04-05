import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem mul_not_equiv_zero {f g : CauSeq _ abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : ¬f * g ≈ 0 := fun (this : CauSeq.LimZero (f * g - 0)) => by
  have hlz : CauSeq.LimZero (f * g) := by simpa
  have hf' : ¬CauSeq.LimZero f := by simpa using show ¬CauSeq.LimZero (f - 0) from hf
  have hg' : ¬CauSeq.LimZero g := by simpa using show ¬CauSeq.LimZero (g - 0) from hg
  rcases CauSeq.abv_pos_of_not_limZero hf' with ⟨a1, ha1, N1, hN1⟩
  rcases CauSeq.abv_pos_of_not_limZero hg' with ⟨a2, ha2, N2, hN2⟩
  have : 0 < a1 * a2 := mul_pos ha1 ha2
  obtain ⟨N, hN⟩ := hlz _ this
  let i := max N (max N1 N2)
  have hN' := hN i (le_max_left _ _)
  have hN1' := hN1 i (le_trans (le_max_left _ _) (le_max_right _ _))
  have hN1' := hN2 i (le_trans (le_max_right _ _) (le_max_right _ _))
  apply not_le_of_gt hN'
  change _ ≤ abv (_ * _)
  rw [abv_mul abv]
  gcongr

