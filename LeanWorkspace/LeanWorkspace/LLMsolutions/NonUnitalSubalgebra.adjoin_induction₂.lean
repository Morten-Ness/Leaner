FAIL
import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_induction₂ {s : Set A} {p : ∀ x y, x ∈ NonUnitalAlgebra.adjoin R s → y ∈ NonUnitalAlgebra.adjoin R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (NonUnitalAlgebra.subset_adjoin R hx) (NonUnitalAlgebra.subset_adjoin R hy))
    (zero_left : ∀ x hx, p 0 x (zero_mem _) hx) (zero_right : ∀ x hx, p x 0 hx (zero_mem _))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    (smul_left : ∀ r x y hx hy, p x y hx hy → p (r • x) y (SMulMemClass.smul_mem r hx) hy)
    (smul_right : ∀ r x y hx hy, p x y hx hy → p x (r • y) hx (SMulMemClass.smul_mem r hy))
    {x y : A} (hx : x ∈ NonUnitalAlgebra.adjoin R s) (hy : y ∈ NonUnitalAlgebra.adjoin R s) :
    p x y hx hy := by
  let q : A → Prop := fun x => ∀ y (hy : y ∈ NonUnitalAlgebra.adjoin R s), ∀ hx' : x ∈ NonUnitalAlgebra.adjoin R s, p x y hx' hy
  have hmem : ∀ x ∈ s, q x := by
    intro x hxS y hyS hxA
    have hxA' : x ∈ NonUnitalAlgebra.adjoin R s := NonUnitalAlgebra.subset_adjoin R hxS
    exact
      cast (by cases Subsingleton.elim hxA hxA'; rfl) (mem_mem x y hxS ?_)
    where
      _ : y ∈ s := by
        sorry
  have hzero : q 0 := by
    intro y hyS hx0
    exact zero_left y hyS
  have hadd : ∀ a b, q a → q b → q (a + b) := by
    intro a b ha hb y hyS hsum
    have ha' : a ∈ NonUnitalAlgebra.adjoin R s := by
      exact (show a ∈ NonUnitalAlgebra.adjoin R s from by
        have : a + b ∈ NonUnitalAlgebra.adjoin R s := hsum
        exact (NonUnitalAlgebra.adjoin R s).add_mem ?_ ?_)
    have hb' : b ∈ NonUnitalAlgebra.adjoin R s := by
      exact (show b ∈ NonUnitalAlgebra.adjoin R s from by
        have : a + b ∈ NonUnitalAlgebra.adjoin R s := hsum
        exact (NonUnitalAlgebra.adjoin R s).add_mem ?_ ?_)
    exact add_left a b y ha' hb' hyS (ha y hyS ha') (hb y hyS hb')
  have hmul : ∀ a b, q a → q b → q (a * b) := by
    intro a b ha hb y hyS hmulab
    have ha' : a ∈ NonUnitalAlgebra.adjoin R s := by
      exact NonUnitalAlgebra.mul_mem_left (s := NonUnitalAlgebra.adjoin R s) ?_ hmulab
    have hb' : b ∈ NonUnitalAlgebra.adjoin R s := by
      exact NonUnitalAlgebra.mul_mem_right (s := NonUnitalAlgebra.adjoin R s) ?_ hmulab
    exact mul_left a b y ha' hb' hyS (ha y hyS ha') (hb y hyS hb')
  have hsmul : ∀ r a, q a → q (r • a) := by
    intro r a ha y hyS hs
    have ha' : a ∈ NonUnitalAlgebra.adjoin R s := by
      sorry
    exact smul_left r a y ha' hyS (ha y hyS ha')
  have hxq : q x := by
    refine NonUnitalAlgebra.adjoin_induction (R := R) (s := s) (p := q) hx ?_ ?_ ?_ ?_ ?_
    · exact hmem
    · exact hzero
    · intro a b ha hb
      exact hadd a b ha hb
    · intro a b ha hb
      exact hmul a b ha hb
    · intro r a ha
      exact hsmul r a ha
  exact hxq y hy hx
