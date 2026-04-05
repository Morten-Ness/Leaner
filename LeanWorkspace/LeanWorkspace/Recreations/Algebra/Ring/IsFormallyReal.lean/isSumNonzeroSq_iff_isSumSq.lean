import Mathlib

variable {R : Type*}

theorem isSumNonzeroSq_iff_isSumSq [NonUnitalNonAssocSemiring R] {s : R} (hs : s ≠ 0) :
    IsSumNonzeroSq s ↔ IsSumSq s where
  mp := IsSumNonzeroSq.isSumSq
  mpr h := by
    induction h with
    | zero => grind
    | @sq_add a s hs ih =>
    rcases eq_or_ne a 0 with (rfl | ne_a)
    · simp_all
    · rcases eq_or_ne s 0 with (rfl | ne_s)
      · simpa using IsSumNonzeroSq.sq ne_a
      · exact IsSumNonzeroSq.sq_add ne_a (ih ne_s)

alias ⟨_, IsSumSq.isSumNonzeroSq_of_ne_zero⟩ := isSumNonzeroSq_iff_isSumSq

