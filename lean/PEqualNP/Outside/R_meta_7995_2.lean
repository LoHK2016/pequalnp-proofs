import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_7995_2
    (h_lower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.TopForm.IsAO2 (14 : ℕ) C →
  (∀ (x5 : Fin (14 : ℕ) → Bool), C.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) →
  (25 : ℕ) ≤ C.size)
    (h_clash : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s : ℕ),
  C.size ≤ s → (s + 1 : ℕ) ≤ C.size → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (24 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → False :=
by
  classical
  intro x1 hsize hAO hdist heval
  have hbig : (25 : ℕ) ≤ x1.size := h_lower x1 hAO heval
  exact h_clash x1 24 hsize hbig
