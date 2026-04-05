import Mathlib

variable {R M : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

variable {I : Ideal R} {r : R}

theorem isTorsionBy_quotient_iff (N : Submodule R M) (r : R) :
    IsTorsionBy R (M ⧸ N) r ↔ ∀ x, r • x ∈ N := Iff.trans N.mkQ_surjective.forall <| forall_congr' fun _ =>
    Submodule.Quotient.mk_eq_zero N

