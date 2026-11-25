import Mathlib
import PEqualNP.Defs

-- L-meta-6202: 存在一个小的 top-form AND/OR 电路计算给定边函数。
-- 切成两块：
--   (1) 存在满足结构约束（top-form、无重入线、输出在范围内、门数上界）的电路；
--   (2) 任何满足这些结构约束的电路都在给定条件下功能正确。
-- 结论逐字等于原 step；(1) 给出见证，(2) 把见证补上功能正确性。
theorem PEqualNP.Outside.R_meta_6202_1
    (hWitness : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (13 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ x1.output < (13 : ℕ) + x1.size ∧ x1.size ≤ (14 : ℕ))
    (hFunctional : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.TopForm.IsAO2 (13 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ x1.output < (13 : ℕ) + x1.size ∧ x1.size ≤ (14 : ℕ)) → (∀ (x2 : Fin (14 : ℕ) → Bool), (x2 (0 : Fin (14 : ℕ)) && (x2 (8 : Fin (14 : ℕ)) || x2 (10 : Fin (14 : ℕ)) || x2 (7 : Fin (14 : ℕ))) || x2 (1 : Fin (14 : ℕ)) && (x2 (9 : Fin (14 : ℕ)) || x2 (13 : Fin (14 : ℕ)) || x2 (7 : Fin (14 : ℕ))) || x2 (3 : Fin (14 : ℕ)) && (x2 (11 : Fin (14 : ℕ)) || x2 (12 : Fin (14 : ℕ)) || x2 (7 : Fin (14 : ℕ)))) = Bool.false → (x1.eval [x2 (2 : Fin (14 : ℕ)), x2 (4 : Fin (14 : ℕ)), x2 (5 : Fin (14 : ℕ)), x2 (6 : Fin (14 : ℕ)), x2 (8 : Fin (14 : ℕ)), x2 (9 : Fin (14 : ℕ)), x2 (10 : Fin (14 : ℕ)), x2 (11 : Fin (14 : ℕ)), x2 (12 : Fin (14 : ℕ)), x2 (13 : Fin (14 : ℕ)), x2 (8 : Fin (14 : ℕ)) || x2 (10 : Fin (14 : ℕ)), x2 (9 : Fin (14 : ℕ)) || x2 (13 : Fin (14 : ℕ)), x2 (11 : Fin (14 : ℕ)) || x2 (12 : Fin (14 : ℕ))] = Bool.true ↔ ∃ (x4 : Fin (14 : ℕ)) (x5 : Fin (14 : ℕ)), (↑x4, ↑x5) ∈ [((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x2 x4 = Bool.true ∧ x2 x5 = Bool.true))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (13 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ x1.output < (13 : ℕ) + x1.size ∧ x1.size ≤ (14 : ℕ) ∧ ∀ (x2 : Fin (14 : ℕ) → Bool), (x2 (0 : Fin (14 : ℕ)) && (x2 (8 : Fin (14 : ℕ)) || x2 (10 : Fin (14 : ℕ)) || x2 (7 : Fin (14 : ℕ))) || x2 (1 : Fin (14 : ℕ)) && (x2 (9 : Fin (14 : ℕ)) || x2 (13 : Fin (14 : ℕ)) || x2 (7 : Fin (14 : ℕ))) || x2 (3 : Fin (14 : ℕ)) && (x2 (11 : Fin (14 : ℕ)) || x2 (12 : Fin (14 : ℕ)) || x2 (7 : Fin (14 : ℕ)))) = Bool.false → (x1.eval [x2 (2 : Fin (14 : ℕ)), x2 (4 : Fin (14 : ℕ)), x2 (5 : Fin (14 : ℕ)), x2 (6 : Fin (14 : ℕ)), x2 (8 : Fin (14 : ℕ)), x2 (9 : Fin (14 : ℕ)), x2 (10 : Fin (14 : ℕ)), x2 (11 : Fin (14 : ℕ)), x2 (12 : Fin (14 : ℕ)), x2 (13 : Fin (14 : ℕ)), x2 (8 : Fin (14 : ℕ)) || x2 (10 : Fin (14 : ℕ)), x2 (9 : Fin (14 : ℕ)) || x2 (13 : Fin (14 : ℕ)), x2 (11 : Fin (14 : ℕ)) || x2 (12 : Fin (14 : ℕ))] = Bool.true ↔ ∃ (x4 : Fin (14 : ℕ)) (x5 : Fin (14 : ℕ)), (↑x4, ↑x5) ∈ [((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x2 x4 = Bool.true ∧ x2 x5 = Bool.true) := by
  classical
  obtain ⟨C, hstruct⟩ := hWitness
  refine ⟨C, hstruct.1, hstruct.2.1, hstruct.2.2.1, hstruct.2.2.2, ?_⟩
  exact hFunctional C hstruct
