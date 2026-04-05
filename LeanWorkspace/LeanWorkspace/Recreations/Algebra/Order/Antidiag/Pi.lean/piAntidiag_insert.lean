import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCancelCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {i : ι}
  {s : Finset ι}

theorem piAntidiag_insert [DecidableEq (ι → μ)] (hi : i ∉ s) (n : μ) :
    Finset.piAntidiag (insert i s) n = (antidiagonal n).biUnion fun p : μ × μ ↦ (Finset.piAntidiag s p.snd).image
      (fun f j ↦ f j + if j = i then p.fst else 0) := by
  simpa [map_eq_image, addRightEmbedding] using Finset.piAntidiag_cons hi n

