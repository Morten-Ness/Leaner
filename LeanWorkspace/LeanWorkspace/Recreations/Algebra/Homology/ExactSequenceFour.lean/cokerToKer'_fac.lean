import Mathlib

variable {C : Type*} [Category C] [HasZeroMorphisms C] {n : ℕ} {S : ComposableArrows C (n + 3)}
  (hS : S.IsComplex) (k : ℕ)

set_option backward.isDefEq.respectTransparency false in
theorem cokerToKer'_fac (hk : k ≤ n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf) :
    cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι =
      S.map' (k + 1) (k + 2) := by
  simp [CategoryTheory.ComposableArrows.IsComplex.cokerToKer']

