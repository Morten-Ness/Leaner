import Mathlib

open scoped Classical

variable {X G : Type*} {A B C : Set X}

variable [Monoid G] [MulAction G X]

theorem IsDecompOn.comp {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : Equidecomp.IsDecompOn g B T) (hf : Equidecomp.IsDecompOn f A S) (h : MapsTo f A B) :
    Equidecomp.IsDecompOn (g ∘ f) A (T * S) := by
  rw [left_eq_inter.mpr h]
  exact hg.comp' hf

