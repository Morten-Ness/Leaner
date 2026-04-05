import Mathlib

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}

include hS in
theorem span_rightExact {w : ι' → S.X₃} (hv : ⊤ ≤ span R (Set.range v))
    (hw : ⊤ ≤ span R (Set.range w)) (hE : Epi S.g) :
    ⊤ ≤ span R (Set.range (Sum.elim (S.f ∘ v) (S.g.hom.toFun.invFun ∘ w))) := by
  refine ModuleCat.span_exact hS ?_ hv ?_
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inl]
  · convert hw
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inr]
    rw [ModuleCat.epi_iff_surjective] at hE
    rw [← Function.comp_assoc, Function.RightInverse.comp_eq_id (Function.rightInverse_invFun hE),
      Function.id_comp]

