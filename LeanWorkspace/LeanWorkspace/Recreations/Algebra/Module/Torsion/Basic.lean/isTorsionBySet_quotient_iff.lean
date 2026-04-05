import Mathlib

variable {R M : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

variable {I : Ideal R} {r : R}

theorem isTorsionBySet_quotient_iff (N : Submodule R M) (s : Set R) :
    IsTorsionBySet R (M ⧸ N) s ↔ ∀ x, ∀ r ∈ s, r • x ∈ N := Iff.trans N.mkQ_surjective.forall <| forall_congr' fun _ =>
    Iff.trans Subtype.forall <| forall₂_congr fun _ _ =>
      Submodule.Quotient.mk_eq_zero N

