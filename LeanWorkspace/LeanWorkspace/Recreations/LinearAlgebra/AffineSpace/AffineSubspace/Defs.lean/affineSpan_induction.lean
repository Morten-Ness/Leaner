import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

theorem affineSpan_induction {x : P} {s : Set P} {p : P → Prop} (h : x ∈ affineSpan k s)
    (mem : ∀ x : P, x ∈ s → p x)
    (smul_vsub_vadd : ∀ (c : k) (u v w : P), p u → p v → p w → p (c • (u -ᵥ v) +ᵥ w)) : p x := (affineSpan_le (Q := ⟨{x | p x}, smul_vsub_vadd⟩)).mpr mem h

