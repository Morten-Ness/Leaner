FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_induction {p : (x : A) → x ∈ Algebra.adjoin R s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (Algebra.subset_adjoin hx))
    (algebraMap : ∀ r, p (algebraMap R A r) (algebraMap_mem _ r))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x : A} (hx : x ∈ Algebra.adjoin R s) : p x hx := by
  simpa using
    (Algebra.adjoin_induction
      (K := R) (s := s) (p := fun x => ∀ hx : x ∈ Algebra.adjoin R s, p x hx)
      (fun x hx hx' => by simpa using mem x hx)
      (fun r hx' => by simpa using algebraMap r)
      (fun x y hx hy px py hxy => by
        exact add x y hx hy (px hx) (py hy))
      (fun x y hx hy px py hxy => by
        exact mul x y hx hy (px hx) (py hy))
      hx) hx
