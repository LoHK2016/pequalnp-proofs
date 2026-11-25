import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_8732_1
    (h_min : ∀ (p N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (D : PEqualNP.CircuitLowerBounds.Circuit),
  (2 : ℕ) ≤ p → p ≤ (130 : ℕ) → N = p ^ (2 : ℕ) + p + (1 : ℕ) → (∀ (a : Fin N), Fintype.card { b : Fin N // R b a } = p + (1 : ℕ)) → (∀ (a a' : Fin N), a ≠ a' → ∃! c : Fin N, R a c ∧ R a' c) →
  PEqualNP.MetaComplexity.Monotone2 D →
  (∀ (v : Fin (N + N) → Bool), Fintype.card { w : Fin N // v (Fin.natAdd N w) = Bool.true } ≤ p → (¬∃ (a : Fin N) (b : Fin N), R a b ∧ v (Fin.castAdd N a) = Bool.true ∧ v (Fin.natAdd N b) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (N + N) D v = Bool.false) →
  (∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[k]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  ∃ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 E ∧ E.size ≤ D.size ∧
    (∀ D' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D' → (∀ (v : Fin (N + N) → Bool), Fintype.card { w : Fin N // v (Fin.natAdd N w) = Bool.true } ≤ p → (¬∃ (a : Fin N) (b : Fin N), R a b ∧ v (Fin.castAdd N a) = Bool.true ∧ v (Fin.natAdd N b) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (N + N) D' v = Bool.false) → E.size ≤ D'.size))
    (h_count : ∀ (p N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (D E : PEqualNP.CircuitLowerBounds.Circuit),
  E.size ≤ D.size →
  (2 : ℕ) ≤ p → p ≤ (130 : ℕ) → N = p ^ (2 : ℕ) + p + (1 : ℕ) → (∀ (a : Fin N), Fintype.card { b : Fin N // R b a } = p + (1 : ℕ)) → (∀ (a a' : Fin N), a ≠ a' → ∃! c : Fin N, R a c ∧ R a' c) →
  PEqualNP.MetaComplexity.Monotone2 D →
  (∀ (v : Fin (N + N) → Bool), Fintype.card { w : Fin N // v (Fin.natAdd N w) = Bool.true } ≤ p → (¬∃ (a : Fin N) (b : Fin N), R a b ∧ v (Fin.castAdd N a) = Bool.true ∧ v (Fin.natAdd N b) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (N + N) D v = Bool.false) →
  (∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), D.gates[k]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  Fintype.card { x14 : Fin N × Fin N // R x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (N + N) D fun (x15 : Fin (N + N)) => Decidable.decide (x15 = Fin.castAdd N x14.1 ∨ x15 = Fin.natAdd N x14.2)) = Bool.true } ≤ (44 : ℕ) * E.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (130 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → (∃ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x13]? = Option.some x14 ∧ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) → Fintype.card { x14 : Fin x2 × Fin x2 // x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x14.1 ∨ x15 = Fin.natAdd x2 x14.2)) = Bool.true } ≤ (44 : ℕ) * x5.size :=
by
  classical
  intro x1 x2 x3 x4 x5 h2 h130 hN hlines huniq hmono hfalse hor
  obtain ⟨E, hEmono, hEle, hEmin⟩ := h_min x1 x2 x3 x5 h2 h130 hN hlines huniq hmono hfalse hor
  have hc := h_count x1 x2 x3 x5 E hEle h2 h130 hN hlines huniq hmono hfalse hor
  exact le_trans hc (Nat.mul_le_mul_left 44 hEle)
