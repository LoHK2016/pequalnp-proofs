import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_9433_2
    (h_c1 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)) t → t < (14 : ℕ) → (14 : ℕ) ≤ t)
    (h_c2 : ∀ t : ℕ, ¬ t < (14 : ℕ) → (14 : ℕ) ≤ t) :
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)) t → 14 ≤ t :=
by
  classical
  intro t hcs
  by_cases hsmall : t < (14 : ℕ)
  · exact h_c1 t hcs hsmall
  · exact h_c2 t hsmall
