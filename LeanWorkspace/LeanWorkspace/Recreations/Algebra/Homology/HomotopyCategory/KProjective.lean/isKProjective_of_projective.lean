import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
theorem isKProjective_of_projective (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ (n : ℤ), Projective (K.X n)] :
    K.IsKProjective := by
  let L := ((opEquivalence C).functor.obj (op K))
  have (n : ℤ) : Function.Injective (L.X n) := by
    dsimp [L]
    infer_instance
  have : L.IsStrictlyGE (-d) := by
    rw [isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE d _ (by dsimp; lia)).op
  exact CochainComplex.isKProjective_of_op (isKInjective_of_injective L (-d))

