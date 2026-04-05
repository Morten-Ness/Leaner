import Mathlib

variable {I : Type u}

variable {f : I → Type v}

theorem single_smul₀ {g : I → Type*} [∀ i, MonoidWithZero (f i)] [∀ i, AddMonoid (g i)]
    [∀ i, DistribMulAction (f i) (g i)] [DecidableEq I] (i : I) (r : f i) (x : g i) :
    single i (r • x) = single i r • single i x := single_op₂ (fun i : I => ((· • ·) : f i → g i → g i)) (fun _ => smul_zero _) _ _ _

