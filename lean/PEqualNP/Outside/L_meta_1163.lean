import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1163

lemma monotone2_c : PEqualNP.MetaComplexity.Monotone2
    ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

end PEqualNP.Outside.L_meta_1163

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_1163 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x :=
  ⟨{ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩,
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], output := 16 }, PEqualNP.Outside.L_meta_1163.monotone2_c, by decide, by decide⟩
