import Mathlib

universe uR uS uA uB

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
  let q : ∀ x : A, x ∈ Algebra.adjoin R s → Prop :=
    fun x hx => ∀ ⦃y : A⦄, ∀ hy : y ∈ Algebra.adjoin R s, p x y hx hy
  have hxq : q x hx := by
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · intro x hx
      dsimp [q]
      intro y hy
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hy
      · intro y hy'
        exact mem_mem x y hx hy'
      · intro r
        exact algebraMap_right r x hx
      · intro y₁ y₂ hy₁ hy₂ ih₁ ih₂
        exact add_right x y₁ y₂ (Algebra.subset_adjoin hx) hy₁ hy₂ ih₁ ih₂
      · intro y₁ y₂ hy₁ hy₂ ih₁ ih₂
        exact mul_right x y₁ y₂ (Algebra.subset_adjoin hx) hy₁ hy₂ ih₁ ih₂
    · intro r
      dsimp [q]
      intro y hy
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hy
      · intro y hy'
        exact algebraMap_left r y hy'
      · intro r'
        exact algebraMap_both r r'
      · intro y₁ y₂ hy₁ hy₂ ih₁ ih₂
        exact add_right (algebraMap R A r) y₁ y₂ (algebraMap_mem _ r) hy₁ hy₂ ih₁ ih₂
      · intro y₁ y₂ hy₁ hy₂ ih₁ ih₂
        exact mul_right (algebraMap R A r) y₁ y₂ (algebraMap_mem _ r) hy₁ hy₂ ih₁ ih₂
    · intro x₁ x₂ hx₁ hx₂ ih₁ ih₂
      dsimp [q] at ih₁ ih₂ ⊢
      intro y hy
      exact add_left x₁ x₂ y hx₁ hx₂ hy (ih₁ hy) (ih₂ hy)
    · intro x₁ x₂ hx₁ hx₂ ih₁ ih₂
      dsimp [q] at ih₁ ih₂ ⊢
      intro y hy
      exact mul_left x₁ x₂ y hx₁ hx₂ hy (ih₁ hy) (ih₂ hy)
  exact hxq hy
