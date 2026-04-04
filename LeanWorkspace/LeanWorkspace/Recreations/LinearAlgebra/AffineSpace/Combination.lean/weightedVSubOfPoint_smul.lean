import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_smul {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
    (s : Finset ι) (w : ι → k) (p : ι → V) (b : V) (a : G) :
    s.weightedVSubOfPoint (a • p) b w = a • s.weightedVSubOfPoint p (a⁻¹ • b) w := by
  simp [smul_sum, smul_sub, smul_comm a (w _)]

