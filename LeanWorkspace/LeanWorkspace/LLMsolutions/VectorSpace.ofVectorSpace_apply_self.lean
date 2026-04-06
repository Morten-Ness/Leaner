FAIL
import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem ofVectorSpace_apply_self (x : Module.Basis.ofVectorSpaceIndex K V) : Module.Basis.ofVectorSpace K V x = x := by
  simpa [Module.Basis.ofVectorSpace] using
    Module.Basis.extend_apply_self (K := K) (s := (∅ : Set V))
      (hs := linearIndepOn_empty_id) x
