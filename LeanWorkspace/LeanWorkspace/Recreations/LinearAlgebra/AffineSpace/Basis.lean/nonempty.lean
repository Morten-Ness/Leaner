import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem nonempty : Nonempty ι := not_isEmpty_iff.mp fun hι => by
    simpa only [@range_eq_empty _ _ hι, AffineSubspace.span_empty, bot_ne_top] using AffineBasis.tot b

