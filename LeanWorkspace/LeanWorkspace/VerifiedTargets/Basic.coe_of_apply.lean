import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

theorem coe_of_apply {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] {A : ι → S} (i j : ι) (x : A i) :
    (DirectSum.of (fun i ↦ {x // x ∈ A i}) i x j : M) = if i = j then x else 0 := by
  obtain rfl | h := Decidable.eq_or_ne j i
  · rw [DirectSum.of_eq_same, if_pos rfl]
  · rw [DirectSum.of_eq_of_ne _ _ _ h, if_neg h.symm, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]

