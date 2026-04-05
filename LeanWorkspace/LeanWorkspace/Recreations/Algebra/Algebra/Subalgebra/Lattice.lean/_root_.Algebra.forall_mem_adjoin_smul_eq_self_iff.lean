import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem _root_.Algebra.forall_mem_adjoin_smul_eq_self_iff (S : Set A) {M : Type*} [Monoid M]
    [MulSemiringAction M A] [SMulCommClass M R A] (m : M) :
    (∀ x ∈ Algebra.adjoin R S, m • x = x) ↔ (∀ x ∈ S, m • x = x) := AlgHom.eqOn_adjoin_iff (φ := MulSemiringAction.toAlgHom R A m) (ψ := .id R A)

