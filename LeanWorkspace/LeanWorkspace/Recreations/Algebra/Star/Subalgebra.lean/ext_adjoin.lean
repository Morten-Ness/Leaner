import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A]

variable [Semiring B] [Algebra R B] [StarRing B]

variable [StarModule R A]

theorem ext_adjoin {s : Set A} [FunLike F (StarAlgebra.adjoin R s) B]
    [AlgHomClass F R (StarAlgebra.adjoin R s) B] [StarHomClass F (StarAlgebra.adjoin R s) B] {f g : F}
    (h : ∀ x : StarAlgebra.adjoin R s, (x : A) ∈ s → f x = g x) : f = g := by
  refine DFunLike.ext f g fun a =>
    StarAlgebra.adjoin_induction_subtype (p := fun y => f y = g y) a (fun x hx => ?_) (fun r => ?_)
    (fun x y hx hy => ?_) (fun x y hx hy => ?_) fun x hx => ?_
  · exact h ⟨x, StarAlgebra.subset_adjoin R s hx⟩ hx
  · simp only [AlgHomClass.commutes]
  · simp only [map_add, map_add, hx, hy]
  · simp only [map_mul, map_mul, hx, hy]
  · simp only [map_star, hx]

