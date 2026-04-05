import Mathlib

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}

variable (hv : LinearIndependent R v) {u : ι ⊕ ι' → S.X₂}
  (hw : LinearIndependent R (S.g ∘ u ∘ Sum.inr))
  (hm : Mono S.f) (huv : u ∘ Sum.inl = S.f ∘ v)

include hS' hv in
theorem linearIndependent_shortExact {w : ι' → S.X₃} (hw : LinearIndependent R w) :
    LinearIndependent R (Sum.elim (S.f ∘ v) (S.g.hom.toFun.invFun ∘ w)) := by
  apply ModuleCat.linearIndependent_leftExact hS'.exact hv _ hS'.mono_f rfl
  dsimp
  convert hw
  ext
  apply Function.rightInverse_invFun ((epi_iff_surjective _).mp hS'.epi_g)

