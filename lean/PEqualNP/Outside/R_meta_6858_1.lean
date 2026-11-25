import Mathlib
import PEqualNP.Defs

-- L-meta-6858: 存在一个 Monotone2 且 size<=68 的电路计算给定边函数。
-- 切成两块：
--   (1) 存在满足结构约束（Monotone2、size 上界）的电路（构造搜索）；
--   (2) 任何满足该结构约束的电路都满足功能正确性条件。
-- 结论逐字等于原 step；(1) 给见证，(2) 补功能条件。
theorem PEqualNP.Outside.R_meta_6858_1
    (hWitness : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (68 : ℕ))
    (hFunctional : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (68 : ℕ)) → (∀ (x2 : Fin (42 : ℕ) → Bool),         have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) => x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));         x1.eval ((List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ)) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ ↑x4 % (3 : ℕ) ≠ (2 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x4 = Bool.true ∧ x2 x5 = Bool.true)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (68 : ℕ) ∧       ∀ (x2 : Fin (42 : ℕ) → Bool),         have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) => x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));         x1.eval ((List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ)) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ ↑x4 % (3 : ℕ) ≠ (2 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x4 = Bool.true ∧ x2 x5 = Bool.true := by
  classical
  obtain ⟨C, hstruct⟩ := hWitness
  refine ⟨C, hstruct.1, hstruct.2, ?_⟩
  exact hFunctional C hstruct
