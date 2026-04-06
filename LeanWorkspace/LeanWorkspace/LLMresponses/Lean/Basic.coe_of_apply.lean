FAIL
import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

theorem coe_of_apply {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] {A : ι → S} (i j : ι) (x : A i) :
    (DirectSum.of (fun i ↦ {x // x ∈ A i}) i x j : M) = if i = j then x else 0 := by
  classical
  by_cases h : i = j
  · subst h
    simp [DirectSum.of]
  · simp [DirectSum.of, h]
