import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {s : Set P}

theorem affineSpan_nonempty : (affineSpan k s : Set P).Nonempty ↔ s.Nonempty := spanPoints_nonempty k s

alias ⟨_, _root_.Set.Nonempty.affineSpan⟩ := affineSpan_nonempty

