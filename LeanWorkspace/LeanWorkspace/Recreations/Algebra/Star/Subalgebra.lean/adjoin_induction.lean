import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_induction {s : Set A} {p : (x : A) → x ∈ StarAlgebra.adjoin R s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (StarAlgebra.subset_adjoin R s h))
    (algebraMap : ∀ r, p (_root_.algebraMap R _ r) (StarSubalgebra.algebraMap_mem _root_ _ r))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (star : ∀ x hx, p x hx → p (star x) (star_mem hx))
    {a : A} (ha : a ∈ StarAlgebra.adjoin R s) : p a ha := by
  refine Algebra.adjoin_induction (fun x hx ↦ ?_) algebraMap add mul ha
  push _ ∈ _ at hx
  obtain (hx | hx) := hx
  · exact mem x hx
  · simpa using star _ (Algebra.subset_adjoin (by simpa using Or.inl hx)) (mem _ hx)

