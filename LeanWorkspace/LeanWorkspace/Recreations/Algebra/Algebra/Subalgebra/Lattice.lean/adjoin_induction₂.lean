import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_induction₂ {s : Set A} {p : (x y : A) → x ∈ Algebra.adjoin R s → y ∈ Algebra.adjoin R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (Algebra.subset_adjoin hx) (Algebra.subset_adjoin hy))
    (algebraMap_both : ∀ r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂) (algebraMap_mem _ r₁)
      (algebraMap_mem _ r₂))
    (algebraMap_left : ∀ (r) (x) (hx : x ∈ s), p (algebraMap R A r) x (algebraMap_mem _ r)
      (Algebra.subset_adjoin hx))
    (algebraMap_right : ∀ (r) (x) (hx : x ∈ s), p x (algebraMap R A r) (Algebra.subset_adjoin hx)
      (algebraMap_mem _ r))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    {x y : A} (hx : x ∈ Algebra.adjoin R s) (hy : y ∈ Algebra.adjoin R s) :
    p x y hx hy := by
  induction hy using Algebra.adjoin_induction with
  | mem z hz => induction hx using Algebra.adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | algebraMap r =>
    induction hx using Algebra.adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂

