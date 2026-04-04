import Mathlib

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

variable (k P1)

variable {k P1}

variable {P1}

variable {k}

variable (k) in

variable {ι : Type*} {V : ι → Type*} {P : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)] [∀ i, AddTorsor (V i) (P i)]

theorem pi_lineMap_apply (f g : ∀ i, P i) (c : k) (i : ι) :
    AffineMap.lineMap f g c i = AffineMap.lineMap (f i) (g i) c := (AffineMap.proj i : (∀ i, P i) →ᵃ[k] P i).apply_lineMap f g c

