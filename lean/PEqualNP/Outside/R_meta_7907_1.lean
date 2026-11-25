import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_7907_1
    (h_count : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (300 : ℕ) ≤ x1 → x1 ≤ (399 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → Fintype.card { p : Fin x2 × Fin x2 // x3 p.1 p.2 } = x2 * x1)
    (h_cap : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x1 ≤ (399 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x14 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x14 ∧ x14.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x15]? = Option.some x16 → ∃ (x18 : ℕ) (x19 : ℕ), x16.inputs = [x18, x19] ∧ x18 < x19 ∧ x19 < x2 + x2 + x15) → (∀ (x16 x17 : Fin x2), x3 x16 x17 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x19 : Fin (x2 + x2)) => Decidable.decide (x19 = Fin.castAdd x2 x16 ∨ x19 = Fin.natAdd x2 x17)) = Bool.true) → (∀ (x17 : Fin (x2 + x2) → Bool), Fintype.card { x18 : Fin x2 // x17 (Fin.natAdd x2 x18) = Bool.true } ≤ x1 → (¬∃ (x19 : Fin x2) (x20 : Fin x2), x3 x19 x20 ∧ x17 (Fin.castAdd x2 x19) = Bool.true ∧ x17 (Fin.natAdd x2 x20) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x17 = Bool.false) → Fintype.card { p : Fin x2 × Fin x2 // x3 p.1 p.2 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (fun (z : Fin (x2 + x2)) => Decidable.decide (z = Fin.castAdd x2 p.1 ∨ z = Fin.natAdd x2 p.2)) = Bool.true } ≤ (100 : ℕ) * x5.size)
    (h_all : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x16 x17 : Fin x2), x3 x16 x17 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x19 : Fin (x2 + x2)) => Decidable.decide (x19 = Fin.castAdd x2 x16 ∨ x19 = Fin.natAdd x2 x17)) = Bool.true) → ∀ p : Fin x2 × Fin x2, x3 p.1 p.2 → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (fun (z : Fin (x2 + x2)) => Decidable.decide (z = Fin.castAdd x2 p.1 ∨ z = Fin.natAdd x2 p.2)) = Bool.true)
    : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x1 ≤ (399 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x14 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x14 ∧ x14.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x15]? = Option.some x16 → ∃ (x18 : ℕ) (x19 : ℕ), x16.inputs = [x18, x19] ∧ x18 < x19 ∧ x19 < x2 + x2 + x15) → (∀ (x16 x17 : Fin x2), x3 x16 x17 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x19 : Fin (x2 + x2)) => Decidable.decide (x19 = Fin.castAdd x2 x16 ∨ x19 = Fin.natAdd x2 x17)) = Bool.true) → (∀ (x17 : Fin (x2 + x2) → Bool), Fintype.card { x18 : Fin x2 // x17 (Fin.natAdd x2 x18) = Bool.true } ≤ x1 → (¬∃ (x19 : Fin x2) (x20 : Fin x2), x3 x19 x20 ∧ x17 (Fin.castAdd x2 x19) = Bool.true ∧ x17 (Fin.natAdd x2 x20) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x17 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro x1 x2 x3 inst x5 h300 hle hn hlin huniq hmono hout hlt hgate hfanin hpos hrej
  let A : Finset (Fin x2 × Fin x2) := Finset.univ.filter (fun p => x3 p.1 p.2)
  have hAcard : A.card = x2 * x1 := by
    simpa [A, Fintype.card_subtype] using h_count x1 x2 x3 h300 hle hn hlin huniq
  have hAacc : ∀ p ∈ A, PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (fun (z : Fin (x2 + x2)) => Decidable.decide (z = Fin.castAdd x2 p.1 ∨ z = Fin.natAdd x2 p.2)) = Bool.true := by
    intro p hp
    have hp3 : x3 p.1 p.2 := (Finset.mem_filter.mp hp).2
    exact h_all x1 x2 x3 x5 hn hpos p hp3
  have hsub : A ⊆ Finset.univ.filter (fun p : Fin x2 × Fin x2 => x3 p.1 p.2 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (fun (z : Fin (x2 + x2)) => Decidable.decide (z = Fin.castAdd x2 p.1 ∨ z = Fin.natAdd x2 p.2)) = Bool.true) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, (Finset.mem_filter.mp hp).2, hAacc p hp⟩
  have hcardle : A.card ≤ (Finset.univ.filter (fun p : Fin x2 × Fin x2 => x3 p.1 p.2 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (fun (z : Fin (x2 + x2)) => Decidable.decide (z = Fin.castAdd x2 p.1 ∨ z = Fin.natAdd x2 p.2)) = Bool.true)).card := Finset.card_le_card hsub
  have hbound := h_cap x1 x2 x3 x5 h300 hle hn hmono hout hlt hgate hfanin hpos hrej
  have hft : Fintype.card { p : Fin x2 × Fin x2 // x3 p.1 p.2 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (fun (z : Fin (x2 + x2)) => Decidable.decide (z = Fin.castAdd x2 p.1 ∨ z = Fin.natAdd x2 p.2)) = Bool.true } ≤ (100 : ℕ) * x5.size := by
    simpa using hbound
  have hcard : (Finset.univ.filter (fun p : Fin x2 × Fin x2 => x3 p.1 p.2 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (fun (z : Fin (x2 + x2)) => Decidable.decide (z = Fin.castAdd x2 p.1 ∨ z = Fin.natAdd x2 p.2)) = Bool.true)).card ≤ (100 : ℕ) * x5.size := by
    simpa [Fintype.card_subtype] using hft
  omega

