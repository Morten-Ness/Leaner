import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AddTorsor (φv i) (φp i)]

variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

theorem pi_ext_nonempty [Nonempty ι] (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) :
    f = g := by
  ext i x
  simpa using h i x
