import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable (F E : Type*) {K : Type*} [CommSemiring E] [Semiring K] [SMul F E] [Algebra E K]

theorem Submonoid.adjoin_eq_span_of_eq_span [Semiring F] [Module F K] [IsScalarTower F E K]
    (L : Submonoid K) {S : Set K} (h : (L : Set K) = span F S) :
    toSubmodule (Algebra.adjoin E (L : Set K)) = span E S := by
  rw [Algebra.adjoin_eq_span, L.closure_eq, h]
  exact (span_le.mpr <| span_subset_span _ _ _).antisymm (span_mono subset_span)

