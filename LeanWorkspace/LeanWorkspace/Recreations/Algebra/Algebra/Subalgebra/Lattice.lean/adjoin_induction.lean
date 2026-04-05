import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_induction {p : (x : A) → x ∈ Algebra.adjoin R s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (Algebra.subset_adjoin hx))
    (algebraMap : ∀ r, p (algebraMap R A r) (algebraMap_mem _ r))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x : A} (hx : x ∈ Algebra.adjoin R s) : p x hx := let S : Subalgebra R A :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, add _ _ _ _ hpx hpy⟩
      algebraMap_mem' := fun r ↦ ⟨_, algebraMap r⟩ }
  Algebra.adjoin_le (S := S) (fun y hy ↦ ⟨Algebra.subset_adjoin hy, mem y hy⟩) hx |>.elim fun _ ↦ _root_.id

