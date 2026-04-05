import Mathlib

variable {C : Type*} [Category C] [Preadditive C] {n : ℕ} {S : ComposableArrows C (n + 3)}

variable (hS : S.IsComplex) (k : ℕ) (hk : k ≤ n)
  (cc : CokernelCofork (S.map' k (k + 1))) (kf : KernelFork (S.map' (k + 2) (k + 3)))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

set_option backward.isDefEq.respectTransparency false in
theorem mono_cokerToKer' (hS' : (S.sc hS k).Exact) :
    Mono (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  let h := hS'.rightHomologyDataOfIsColimitCokernelCofork cc hcc
  have := h.exact_iff_mono_g'.1 hS'
  have fac : hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι = h.g' := by
    rw [← cancel_epi h.p, h.p_g', ShortComplex.Exact.rightHomologyDataOfIsColimitCokernelCofork_p,
      CategoryTheory.ComposableArrows.IsComplex.cokerToKer'_fac]
  exact mono_of_mono_fac fac

