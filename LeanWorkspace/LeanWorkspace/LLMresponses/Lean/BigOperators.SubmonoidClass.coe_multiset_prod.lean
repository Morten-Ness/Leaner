import Mathlib

variable {M A B : Type*}

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {x : M} {S : B}

theorem coe_multiset_prod {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod := by
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | @cons a m ih =>
      simp [ih]
