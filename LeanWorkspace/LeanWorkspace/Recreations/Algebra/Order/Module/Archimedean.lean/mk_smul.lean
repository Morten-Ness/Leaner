import Mathlib

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable [Module K M] [PosSMulMono K M]

theorem mk_smul (a : M) {k : K} (h : k ≠ 0) : ArchimedeanClass.mk (k • a) = ArchimedeanClass.mk a := by
  have : Nontrivial K := nontrivial_iff.mpr ⟨k, 0, h⟩
  obtain ⟨m, hm⟩ := Archimedean.arch 1 (show 0 < |k| by simpa using h)
  obtain ⟨n, hn⟩ := Archimedean.arch |k| (show 0 < 1 by simp)
  simp_rw [mk_eq_mk, abs_smul]
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · rw [← smul_assoc]
    exact le_smul_of_one_le_left (by simp) hm
  · have : n • |a| = (n • (1 : K)) • |a| := by rw [smul_assoc, one_smul]
    rw [this]
    exact smul_le_smul_of_nonneg_right hn (by simp)

