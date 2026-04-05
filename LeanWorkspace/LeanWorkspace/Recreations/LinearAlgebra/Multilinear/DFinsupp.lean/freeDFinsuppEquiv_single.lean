import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {ι' : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R]
  [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem freeDFinsuppEquiv_single [DecidableEq ι'] (p : (Π i, κ i) × ι') (r : R)
    (x : Π i, Π₀ _ : κ i, R) :
    MultilinearMap.freeDFinsuppEquiv (.single p r) x = r • .single p.2 ((∏ i, (x i) (p.1 i))) := by
  classical
  conv_lhs => rw [← mul_one r, ← smul_eq_mul, DFinsupp.single_smul, map_smul, smul_apply]
  congr
  ext i
  obtain ⟨p, j⟩ := p
  rcases eq_or_ne j i with rfl | h
  · suffices ∀ (l : ι), (x l) (p l) = 0 → 0 = ∏ i, (x i) (p i) by
      simpa [MultilinearMap.freeDFinsuppEquiv_def, MultilinearMap.piRingEquiv, DFinsupp.sigmaCurryEquiv,
        MultilinearMap.fromDFinsuppEquiv_apply]
    exact fun i h ↦ (Finset.prod_eq_zero (Finset.mem_univ i) h).symm
  · simp [MultilinearMap.freeDFinsuppEquiv_def, MultilinearMap.piRingEquiv, DFinsupp.sigmaCurryEquiv,
      MultilinearMap.fromDFinsuppEquiv_apply, h]

