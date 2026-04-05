import Mathlib

variable {C : Type*} [Category C] [Preadditive C] {n : ℕ} {S : ComposableArrows C (n + 3)}

variable (hS : S.IsComplex) (k : ℕ) (hk : k ≤ n)
  (cc : CokernelCofork (S.map' k (k + 1))) (kf : KernelFork (S.map' (k + 2) (k + 3)))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

set_option backward.isDefEq.respectTransparency false in
theorem epi_cokerToKer' (hS' : (S.sc hS (k + 1)).Exact) :
    Epi (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  let h := hS'.leftHomologyDataOfIsLimitKernelFork kf hkf
  have := h.exact_iff_epi_f'.1 hS'
  have fac : cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf = h.f' := by
    rw [← cancel_mono h.i, h.f'_i, ShortComplex.Exact.leftHomologyDataOfIsLimitKernelFork_i,
      assoc, CategoryTheory.ComposableArrows.IsComplex.cokerToKer'_fac]
  exact epi_of_epi_fac fac

