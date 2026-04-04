import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem basisOf_reindex (i : ι') :
    (b.reindex e).basisOf i =
      (b.basisOf <| e.symm i).reindex (e.subtypeEquiv fun _ => e.eq_symm_apply.not) := by
  ext j
  simp

