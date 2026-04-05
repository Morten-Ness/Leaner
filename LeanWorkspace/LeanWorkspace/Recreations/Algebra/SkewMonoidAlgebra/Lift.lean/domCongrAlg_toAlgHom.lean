import Mathlib

variable {k G H : Type*}

variable {A : Type*}

variable [Monoid G] [Monoid H] [Semiring A] [CommSemiring k] [Algebra k A] [MulSemiringAction G A]
  [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A]

theorem domCongrAlg_toAlgHom {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    (SkewMonoidAlgebra.domCongrAlg k A he).toAlgHom = SkewMonoidAlgebra.mapDomainAlgHom k A he := AlgHom.ext <| fun _ ↦ SkewMonoidAlgebra.equivMapDomain_eq_mapDomain _ _

