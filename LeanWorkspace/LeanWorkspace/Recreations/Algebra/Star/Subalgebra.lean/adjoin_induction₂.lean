import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_induction₂ {s : Set A} {p : (x y : A) → x ∈ StarAlgebra.adjoin R s → y ∈ StarAlgebra.adjoin R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (StarAlgebra.subset_adjoin R s hx)
      (StarAlgebra.subset_adjoin R s hy))
    (algebraMap_both : ∀ r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂)
      (StarSubalgebra.algebraMap_mem _root_ _ r₁) (StarSubalgebra.algebraMap_mem _root_ _ r₂))
    (algebraMap_left : ∀ (r) (x) (hx : x ∈ s), p (algebraMap R A r) x (StarSubalgebra.algebraMap_mem _root_ _ r)
      (StarAlgebra.subset_adjoin R s hx))
    (algebraMap_right : ∀ (r) (x) (hx : x ∈ s), p x (algebraMap R A r) (StarAlgebra.subset_adjoin R s hx)
      (StarSubalgebra.algebraMap_mem _root_ _ r))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    (star_left : ∀ x y hx hy, p x y hx hy → p (star x) y (star_mem hx) hy)
    (star_right : ∀ x y hx hy, p x y hx hy → p x (star y) hx (star_mem hy))
    {a b : A} (ha : a ∈ StarAlgebra.adjoin R s) (hb : b ∈ StarAlgebra.adjoin R s) :
    p a b ha hb := by
  induction hb using StarAlgebra.adjoin_induction with
  | mem z hz => induction ha using StarAlgebra.adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | algebraMap r =>
    induction ha using StarAlgebra.adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | star _ _ h => exact star_left _ _ _ _ h
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | star _ _ h => exact star_right _ _ _ _ h

