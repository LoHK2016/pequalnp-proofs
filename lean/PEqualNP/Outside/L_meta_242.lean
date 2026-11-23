import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_242

lemma wires_append_gate (C : BinaryCircuit) (x : List Bool) (g : BinaryGate) :
    (⟨C.gates ++ [g], C.output⟩ : BinaryCircuit).wires x =
      C.wires x ++
        [g.op ((C.wires x).getD g.left false) ((C.wires x).getD g.right false)] := by
  simp [BinaryCircuit.wires, List.foldl_append]

end PEqualNP.Outside.L_meta_242

theorem PEqualNP.Outside.L_meta_242 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
      PEqualNP.MetaComplexity.HasBinarySize n f s →
        PEqualNP.MetaComplexity.HasBinarySize n f (s + 1) := by
  intro n f s h
  obtain ⟨C, hsize, hval⟩ := h
  have hgl : C.gates.length ≤ s := by simpa [BinaryCircuit.size] using hsize
  refine ⟨⟨C.gates ++ [⟨fun _ _ => false, 0, 0⟩], C.output⟩, ?_, ?_⟩
  · simp [BinaryCircuit.size]
    omega
  · intro x
    rw [BinaryCircuit.eval, PEqualNP.Outside.L_meta_242.wires_append_gate]
    change (C.wires (List.ofFn x) ++ [false]).getD C.output false = f x
    have hval' : (C.wires (List.ofFn x)).getD C.output false = f x := by
      simpa [BinaryCircuit.eval] using hval x
    rcases lt_or_ge C.output (C.wires (List.ofFn x)).length with hlt | hge
    · rw [List.getD_append _ _ _ _ hlt]
      exact hval'
    · have hL : (C.wires (List.ofFn x) ++ [false]).getD C.output false = false := by
        by_cases heq : C.output = (C.wires (List.ofFn x)).length
        · rw [heq, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
          rfl
        · rw [List.getD_eq_default]
          simp only [List.length_append, List.length_singleton]
          omega
      rw [hL, ← hval', List.getD_eq_default _ _ hge]
