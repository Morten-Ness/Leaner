import Mathlib

variable {α ι : Type*} [GeneralizedBooleanAlgebra α]

variable [LinearOrder ι] [LocallyFiniteOrderBot ι] [Add ι] [One ι] [SuccAddOrder ι]

theorem partialSups_add_one_eq_sup_disjointed (f : ι → α) (i : ι) :
    partialSups f (i + 1) = partialSups f i ⊔ disjointed f (i + 1) := by
  by_cases hi : IsMax i
  · have : i + 1 = i := by
      have h : i ≤ i + 1 := by
        rw [← Order.succ_eq_add_one]
        apply Order.le_succ
      exact le_antisymm (hi h) h
    simp only [this, left_eq_sup, ge_iff_le, disjointed, sdiff_le_iff]
    apply le_trans (le_partialSups _ _) le_sup_right
  · rw [← Order.succ_eq_add_one, disjointed_succ _ hi]
    simp

protected lemma Monotone.disjointed_add_one_sup {f : ι → α} (hf : Monotone f) (i : ι) :
    disjointed f (i + 1) ⊔ f i = f (i + 1) := by
  simpa only [succ_eq_add_one i] using hf.disjointed_succ_sup i

protected lemma Monotone.disjointed_add_one [NoMaxOrder ι] {f : ι → α} (hf : Monotone f) (i : ι) :
    disjointed f (i + 1) = f (i + 1) \ f i := by
  rw [← succ_eq_add_one, hf.disjointed_succ]
  exact not_isMax i

