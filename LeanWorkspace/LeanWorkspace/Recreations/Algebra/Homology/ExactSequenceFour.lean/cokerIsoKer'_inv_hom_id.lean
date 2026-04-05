import Mathlib

variable {C : Type*} [Category C] [Preadditive C] [Balanced C] {n : ℕ}
  {S : ComposableArrows C (n + 3)} (hS : S.Exact)

variable (k : ℕ) (hk : k ≤ n)
  (cc : CokernelCofork (S.map' k (k + 1))) (kf : KernelFork (S.map' (k + 2) (k + 3)))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

theorem cokerIsoKer'_inv_hom_id :
    (hS.cokerIsoKer' k hk cc kf hcc hkf).inv ≫ hS.cokerToKer' k hk cc kf hcc hkf = 𝟙 _ := (hS.cokerIsoKer' k hk cc kf hcc hkf).inv_hom_id

