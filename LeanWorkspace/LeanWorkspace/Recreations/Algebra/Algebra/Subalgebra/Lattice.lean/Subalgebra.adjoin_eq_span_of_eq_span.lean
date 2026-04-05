import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable (F E : Type*) {K : Type*} [CommSemiring E] [Semiring K] [SMul F E] [Algebra E K]

variable [CommSemiring F] [Algebra F K] [IsScalarTower F E K] (L : Subalgebra F K) {F}

theorem Subalgebra.adjoin_eq_span_of_eq_span {S : Set K} (h : toSubmodule L = span F S) :
    toSubmodule (Algebra.adjoin E (L : Set K)) = span E S := L.toSubmonoid.adjoin_eq_span_of_eq_span F E (congr_arg ((↑) : _ → Set K) h)

