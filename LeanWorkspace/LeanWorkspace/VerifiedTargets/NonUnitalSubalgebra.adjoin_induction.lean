import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_induction {s : Set A} {p : (x : A) → x ∈ NonUnitalAlgebra.adjoin R s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (NonUnitalAlgebra.subset_adjoin R hx))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy)) (zero : p 0 (zero_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (smul : ∀ r x hx, p x hx → p (r • x) (SMulMemClass.smul_mem r hx))
    {x} (hx : x ∈ NonUnitalAlgebra.adjoin R s) : p x hx := let S : NonUnitalSubalgebra R A :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := (Exists.elim · fun _ ha ↦ (Exists.elim · fun _ hb ↦ ⟨_, mul _ _ _ _ ha hb⟩))
      add_mem' := (Exists.elim · fun _ ha ↦ (Exists.elim · fun _ hb ↦ ⟨_, add _ _ _ _ ha hb⟩))
      smul_mem' := fun r ↦ (Exists.elim · fun _ hb ↦ ⟨_, smul r _ _ hb⟩)
      zero_mem' := ⟨_, zero⟩ }
  NonUnitalAlgebra.adjoin_le (S := S) (fun y hy ↦ ⟨NonUnitalAlgebra.subset_adjoin R hy, mem y hy⟩) hx |>.elim fun _ ↦ id

