import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b ∈ Algebra.adjoin R s) (h : ∀ b ∈ s, Commute a b) :
    Commute a b := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r => exact commutes r a |>.symm
  | add y z _ _ hy hz => exact hy.add_right hz
  | mul y z _ _ hy hz => exact hy.mul_right hz

