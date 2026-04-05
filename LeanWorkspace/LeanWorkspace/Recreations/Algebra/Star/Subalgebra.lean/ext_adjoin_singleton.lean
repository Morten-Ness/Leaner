import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A]

variable [Semiring B] [Algebra R B] [StarRing B]

variable [StarModule R A]

theorem ext_adjoin_singleton {a : A} [FunLike F (StarAlgebra.adjoin R ({a} : Set A)) B]
    [AlgHomClass F R (StarAlgebra.adjoin R ({a} : Set A)) B] [StarHomClass F (StarAlgebra.adjoin R ({a} : Set A)) B]
    {f g : F} (h : f ⟨a, StarAlgebra.self_mem_adjoin_singleton R a⟩ = g ⟨a, StarAlgebra.self_mem_adjoin_singleton R a⟩) :
    f = g := StarAlgHom.ext_adjoin fun x hx =>
    (show x = ⟨a, StarAlgebra.self_mem_adjoin_singleton R a⟩ from
          Subtype.ext <| Set.mem_singleton_iff.mp hx).symm ▸
      h

