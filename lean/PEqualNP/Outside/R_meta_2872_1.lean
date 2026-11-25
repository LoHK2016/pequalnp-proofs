import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2872_1
    (h_min : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsAO2 (n + m) C →
  PEqualNP.MetaComplexity.circuitFun (n + m) C = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ a : Fin n, ∃ b : Fin m, (a, b) ∈ E ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.TopForm.IsAO2 (n + m) D ∧
    PEqualNP.MetaComplexity.circuitFun (n + m) D = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ a : Fin n, ∃ b : Fin m, (a, b) ∈ E ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) ∧
    D.size ≤ C.size ∧
    ∀ D' : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (n + m) D' →
      PEqualNP.MetaComplexity.circuitFun (n + m) D' = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ a : Fin n, ∃ b : Fin m, (a, b) ∈ E ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) →
      D.size ≤ D'.size)
    (h_count : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (D : PEqualNP.CircuitLowerBounds.Circuit),
  M ⊆ E →
  (∀ a a' : Fin n, ∀ b b' : Fin m, a ≠ a' → b ≠ b' → ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
  (∀ a ∈ M, ∀ a' ∈ M, a.1 = a'.1 → a = a') →
  (∀ b ∈ M, ∀ b' ∈ M, b.2 = b'.2 → b = b') →
  PEqualNP.TopForm.IsAO2 (n + m) D →
  PEqualNP.MetaComplexity.circuitFun (n + m) D = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ a : Fin n, ∃ b : Fin m, (a, b) ∈ E ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) →
  (∀ D' : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.TopForm.IsAO2 (n + m) D' →
    PEqualNP.MetaComplexity.circuitFun (n + m) D' = (fun z : Fin (n + m) → Bool => Decidable.decide (∃ a : Fin n, ∃ b : Fin m, (a, b) ∈ E ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) →
    D.size ≤ D'.size) →
  E.card + M.card ≤ D.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) :=
by
  classical
  intro x1 x2 x3 x4 x5 h4 hAO hcomp hMsub hMrow hMcol
  let inc : (Fin (x1 + x2) → Bool) → Bool := fun z =>
    Decidable.decide (∃ a : Fin x1, ∃ b : Fin x2, (a, b) ∈ x3 ∧
      z (Fin.castAdd x2 a) = Bool.true ∧ z (Fin.natAdd x1 b) = Bool.true)
  have hcomp' : PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = inc := by
    funext z
    exact hcomp z
  obtain ⟨D, hDao, hDcomp, hDle, hDmin⟩ := h_min x1 x2 x3 x5 hAO hcomp'
  have hb := h_count x1 x2 x3 x4 D hMsub h4 hMrow hMcol hDao hDcomp hDmin
  exact le_trans hb (Nat.add_le_add_right hDle 1)
