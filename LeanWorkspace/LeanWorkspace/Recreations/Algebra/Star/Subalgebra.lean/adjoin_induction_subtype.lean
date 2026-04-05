import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_induction_subtype {s : Set A} {p : StarAlgebra.adjoin R s → Prop} (a : StarAlgebra.adjoin R s)
    (mem : ∀ (x) (h : x ∈ s), p ⟨x, StarAlgebra.subset_adjoin R s h⟩) (algebraMap : ∀ r, p (algebraMap R _ r))
    (add : ∀ x y, p x → p y → p (x + y)) (mul : ∀ x y, p x → p y → p (x * y))
    (star : ∀ x, p x → p (star x)) : p a := Subtype.recOn a fun b hb => by
    induction hb using StarAlgebra.adjoin_induction with
    | mem _ h => exact mem _ h
    | algebraMap _ => exact algebraMap _
    | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add _ _ h₁ h₂
    | star _ _ h => exact star _ h

