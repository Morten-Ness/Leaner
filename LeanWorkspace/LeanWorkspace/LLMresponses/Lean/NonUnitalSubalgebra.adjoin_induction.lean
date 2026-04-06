FAIL
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
    {x} (hx : x ∈ NonUnitalAlgebra.adjoin R s) : p x hx := by
  classical
  let P : NonUnitalSubalgebra R A :=
    { carrier := {x | ∃ hx : x ∈ NonUnitalAlgebra.adjoin R s, p x hx}
      algebraMap_mem' := by
        intro r
        exact ⟨algebraMap_mem (NonUnitalAlgebra.adjoin R s) r, by
          simpa using smul r 1 (algebraMap_mem (NonUnitalAlgebra.adjoin R s) r) (by
            simpa using zero)⟩
      zero_mem' := ⟨zero_mem (NonUnitalAlgebra.adjoin R s), zero⟩
      add_mem' := by
        intro x y hxP hyP
        rcases hxP with ⟨hxA, hpx⟩
        rcases hyP with ⟨hyA, hpy⟩
        exact ⟨add_mem hxA hyA, add x y hxA hyA hpx hpy⟩
      mul_mem' := by
        intro x y hxP hyP
        rcases hxP with ⟨hxA, hpx⟩
        rcases hyP with ⟨hyA, hpy⟩
        exact ⟨mul_mem hxA hyA, mul x y hxA hyA hpx hpy⟩
      smul_mem' := by
        intro r x hxP
        rcases hxP with ⟨hxA, hpx⟩
        exact ⟨SMulMemClass.smul_mem r hxA, smul r x hxA hpx⟩ }
  have hs : s ⊆ P := by
    intro y hy
    exact ⟨NonUnitalAlgebra.subset_adjoin R hy, mem y hy⟩
  have hle : NonUnitalAlgebra.adjoin R s ≤ P := NonUnitalAlgebra.adjoin_le hs
  rcases hle hx with ⟨hx', hp⟩
  exact hp
