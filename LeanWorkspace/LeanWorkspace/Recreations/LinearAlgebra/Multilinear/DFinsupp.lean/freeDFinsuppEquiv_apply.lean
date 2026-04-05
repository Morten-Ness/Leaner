import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {ι' : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R]
  [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem freeDFinsuppEquiv_apply [DecidableEq ι'] [Fintype ι']
    (f : Π₀ (_ : (Π i, κ i) × ι'), R) (x : Π i, Π₀ _ : κ i, R) :
    MultilinearMap.freeDFinsuppEquiv f x = ∑ p, f p • .single p.2 ((∏ i, (x i) (p.1 i))) := by
  apply DFinsupp.induction f
  · simp
  · rintro p r f - - hfx
    simp [Finset.sum_add_distrib, add_smul, hfx]

