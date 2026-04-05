import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem adjoin_induction {s : Set A} {p : (x : A) → x ∈ NonUnitalStarAlgebra.adjoin R s → Prop}
    (mem : ∀ (x : A) (hx : x ∈ s), p x (NonUnitalStarAlgebra.subset_adjoin R s hx))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (zero : p 0 (zero_mem _)) (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (smul : ∀ (r : R) x hx, p x hx → p (r • x) (SMulMemClass.smul_mem r hx))
    (star : ∀ x hx, p x hx → p (star x) (star_mem hx))
    {a : A} (ha : a ∈ NonUnitalStarAlgebra.adjoin R s) : p a ha := by
  refine NonUnitalAlgebra.adjoin_induction (fun x hx ↦ ?_) add zero mul smul ha
  push _ ∈ _ at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (NonUnitalAlgebra.subset_adjoin R (by simpa using Or.inl hx)) (mem _ hx)

