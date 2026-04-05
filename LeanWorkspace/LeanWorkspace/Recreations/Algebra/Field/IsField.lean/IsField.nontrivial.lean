import Mathlib

theorem IsField.nontrivial {R : Type u} [Semiring R] (h : IsField R) : Nontrivial R := ⟨h.exists_pair_ne⟩

