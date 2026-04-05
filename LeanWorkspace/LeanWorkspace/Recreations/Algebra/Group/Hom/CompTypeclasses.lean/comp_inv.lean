import Mathlib

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

theorem comp_inv {φ : M →* N} {ψ : N →* M} (h : Function.RightInverse φ ψ)
    {χ : M →* M} [IsId χ] :
    MonoidHom.CompTriple φ ψ χ where
  comp_eq := by simp only [IsId.eq_id, ← DFunLike.coe_fn_eq, coe_comp, h.id, coe_id]

