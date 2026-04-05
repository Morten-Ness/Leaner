import Mathlib

open scoped Topology

variable {K : Type*} (v : K) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable [Archimedean K]

theorem of_convergence [TopologicalSpace K] [OrderTopology K] :
    Filter.Tendsto (of v).convs Filter.atTop <| 𝓝 v := by
  simpa [LinearOrderedAddCommGroup.tendsto_nhds, abs_sub_comm] using GenContFract.of_convergence_epsilon v

