import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
theorem isKProjective_of_op {K : CochainComplex C ℤ}
    (hK : IsKInjective ((opEquivalence C).functor.obj (op K))) :
    K.IsKProjective where
  nonempty_homotopy_zero {L} f hL := ⟨homotopyUnop ((IsKInjective.homotopyZero
      ((opEquivalence C).functor.map f.op) (acyclic_op hL)).trans
        (.ofEq (by simp)))⟩

