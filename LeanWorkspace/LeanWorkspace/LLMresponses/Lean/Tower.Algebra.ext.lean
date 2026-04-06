FAIL
import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by
      letI := h1
      exact r • x) = (by
      letI := h2
      exact r • x)) : h1 = h2 := by
  letI := h1
  letI := h2
  have hmap : ∀ r : S, @algebraMap S A _ _ h1 r = @algebraMap S A _ _ h2 r := by
    intro r
    simpa [Algebra.smul_def] using h r (1 : A)
  cases h1
  cases h2
  congr
  ext r
  exact hmap r
  all_goals
    apply proof_irrelheq
