import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_aeval {A : Type*} [Semiring A] [Algebra R A] (p : ℕ) (P : R[X]) (r : A) :
    Polynomial.aeval r (Polynomial.expand R p P) = Polynomial.aeval (r ^ p) P := by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [map_add, aeval_add, aeval_add, hf, hg]

