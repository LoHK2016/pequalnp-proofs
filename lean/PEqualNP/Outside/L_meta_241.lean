import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_241

lemma getD_ofFn_false (n : ℕ) (x : Fin n → Bool) (i : ℕ) (h : n ≤ i) :
    (List.ofFn x).getD i false = false := by
  rw [List.getD_eq_default]
  simpa using h

end PEqualNP.Outside.L_meta_241

theorem PEqualNP.Outside.L_meta_241 :
    ∀ n s : ℕ,
      PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => false) s := by
  intro n s
  refine ⟨⟨[], n⟩, by simp [BinaryCircuit.size], ?_⟩
  intro x
  exact PEqualNP.Outside.L_meta_241.getD_ofFn_false n x n (le_refl n)
