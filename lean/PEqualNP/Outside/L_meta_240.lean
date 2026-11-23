import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_240

lemma getD_ofFn_const (n : ℕ) (b : Bool) (i : ℕ) :
    (List.ofFn (fun _ : Fin n => b)).getD i false = if i < n then b else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < n <;> simp [h]

end PEqualNP.Outside.L_meta_240

theorem PEqualNP.Outside.L_meta_240 :
    ∀ n s : ℕ,
      PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => true) s ↔ 1 ≤ s := by
  intro n s
  constructor
  · rintro ⟨C, hsize, hval⟩
    by_contra h1
    have hs : s = 0 := by omega
    have hsz : C.size = 0 := by omega
    have hlen : C.gates = [] := List.eq_nil_of_length_eq_zero (by simpa [BinaryCircuit.size] using hsz)
    have hE : C.eval (List.ofFn (fun _ : Fin n => false)) = false := by
      rw [BinaryCircuit.eval, BinaryCircuit.wires, hlen, List.foldl_nil,
        PEqualNP.Outside.L_meta_240.getD_ofFn_const]
      by_cases h : C.output < n <;> simp [h]
    have hT : C.eval (List.ofFn (fun _ : Fin n => false)) = true := hval _
    rw [hT] at hE
    exact Bool.noConfusion hE
  · intro h1
    refine ⟨⟨[⟨fun _ _ => true, 0, 0⟩], n⟩, ?_, ?_⟩
    · simpa [BinaryCircuit.size] using h1
    · intro x
      rw [BinaryCircuit.eval, BinaryCircuit.wires]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      · simp [List.length_ofFn]
      · simp [List.length_ofFn]
