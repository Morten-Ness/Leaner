import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.mono {s t : Set P}
    (ha : AffineIndependent k (fun x => x : t → P)) (hs : s ⊆ t) :
    AffineIndependent k (fun x => x : s → P) := ha.comp_embedding (s.embeddingOfSubset t hs)

