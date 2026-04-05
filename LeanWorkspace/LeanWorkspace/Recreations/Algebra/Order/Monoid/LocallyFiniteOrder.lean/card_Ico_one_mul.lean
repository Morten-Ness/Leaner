import Mathlib

variable {M : Type*} [CancelCommMonoid M] [LinearOrder M] [IsOrderedMonoid M] [LocallyFiniteOrder M]

theorem card_Ico_one_mul [ExistsMulOfLE M] (a b : M)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    #(Ico 1 (a * b)) = #(Ico 1 a) + #(Ico 1 b) := by
  have : Ico 1 b ∪ Ico (1 * b) (a * b) = Ico 1 (a * b) := by
    simp [Ico_union_Ico, ha, hb, Right.one_le_mul ha hb]
  rw [← this, Finset.card_union, Finset.card_Ico_mul_right]
  simp [add_comm]

