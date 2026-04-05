import Mathlib

variable {m : Type*} [Fintype m] {K : Type u} [Field K]

theorem rank_diagonal [DecidableEq m] [DecidableEq K] (w : m → K) :
    LinearMap.rank (toLin' (diagonal w)) = Fintype.card { i // w i ≠ 0 } := by
  have hu : Set.univ ⊆ { i : m | w i = 0 }ᶜ ∪ { i : m | w i = 0 } := by rw [Set.compl_union_self]
  have hd : Disjoint { i : m | w i ≠ 0 } { i : m | w i = 0 } := disjoint_compl_left
  have B₁ := iSup_range_single_eq_iInf_ker_proj K (fun _ : m => K) hd hu (Set.toFinite _)
  have B₂ := iInfKerProjEquiv K (fun _ ↦ K) hd hu
  rw [LinearMap.rank, Matrix.range_diagonal, B₁, ← @rank_fun' K]
  apply LinearEquiv.rank_eq
  apply B₂

