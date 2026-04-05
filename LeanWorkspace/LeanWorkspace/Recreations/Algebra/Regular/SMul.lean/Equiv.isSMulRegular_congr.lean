import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

theorem Equiv.isSMulRegular_congr {R S M M'} [SMul R M] [SMul S M'] {e : M ≃ M'}
    {r : R} {s : S} (h : ∀ x, e (r • x) = s • e x) :
    IsSMulRegular M r ↔ IsSMulRegular M' s := (e.comp_injective _).symm.trans <|
    (iff_of_eq <| congrArg _ <| funext h).trans <| e.injective_comp _

