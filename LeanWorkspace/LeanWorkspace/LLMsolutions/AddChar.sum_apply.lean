import Mathlib

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem sum_apply (s : Finset ι) (ψ : ι → AddChar A M) (a : A) :
    (∑ i ∈ s, ψ i) a = ∏ i ∈ s, ψ i a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [hi, ih]
