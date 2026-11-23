import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_959

-- One step of the wire list of a circuit: the list grows by one entry, the value of the gate
-- read off the wires that exist before it.

def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl wiresStep x := rfl

lemma length_foldl_wiresStep (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wiresStep]
    omega

lemma getD_foldl_wiresStep (gs : List Gate) (w : List Bool) {i : ℕ} (h : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have h2 : i < (wiresStep w g).length := by
      rw [wiresStep, List.length_append, List.length_singleton]
      omega
    rw [ih _ h2]
    exact List.getD_append w [g.op.eval (g.inputs.map fun j => w.getD j false)] false i h

lemma getD_wiresStep_last (w : List Bool) (g : Gate) :
    (wiresStep w g).getD w.length false = g.op.eval (g.inputs.map fun j => w.getD j false) := by
  simp [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_concat_length]

end PEqualNP.Outside.L_meta_959

theorem PEqualNP.Outside.L_meta_959 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b k : ℕ), C.output = n + k →
      C.gates[k]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a, b] } →
      ∀ z : Fin n → Bool,
        PEqualNP.MetaComplexity.circuitFun n C z = true ↔
          (a < C.output ∧ PEqualNP.MetaComplexity.circuitFun n ⟨C.gates, a⟩ z = true) ∧
            (b < C.output ∧ PEqualNP.MetaComplexity.circuitFun n ⟨C.gates, b⟩ z = true) := by
  intro n C a b k hout hgate z
  have hk : k < C.gates.length := (List.getElem?_eq_some_iff.mp hgate).1
  have hgk : C.gates[k] = (⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ : Gate) :=
    (List.getElem?_eq_some_iff.mp hgate).2
  have hdec : C.gates =
      C.gates.take k ++
        (⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ :: C.gates.drop (k + 1)) := by
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.drop_eq_getElem_cons hk, hgk]
  set y : List Bool := List.ofFn z with hy
  have hylen : y.length = n := by simp [hy]
  set w0 : List Bool := (C.gates.take k).foldl PEqualNP.Outside.L_meta_959.wiresStep y with hw0
  have hw0len : w0.length = n + k := by
    rw [hw0, PEqualNP.Outside.L_meta_959.length_foldl_wiresStep, hylen, List.length_take]
    omega
  have hwy : C.gates.foldl PEqualNP.Outside.L_meta_959.wiresStep y =
      (C.gates.drop (k + 1)).foldl PEqualNP.Outside.L_meta_959.wiresStep
        (PEqualNP.Outside.L_meta_959.wiresStep w0
          ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩) := by
    conv_lhs => rw [hdec]
    rw [List.foldl_append, List.foldl_cons, ← hw0]
  have hval : (C.gates.foldl PEqualNP.Outside.L_meta_959.wiresStep y).getD (n + k) false =
      (w0.getD a false && w0.getD b false) := by
    rw [hwy]
    rw [PEqualNP.Outside.L_meta_959.getD_foldl_wiresStep _ _ (by
      rw [PEqualNP.Outside.L_meta_959.wiresStep, List.length_append, List.length_singleton, hw0len]
      omega)]
    rw [← hw0len, PEqualNP.Outside.L_meta_959.getD_wiresStep_last]
    simp [GateOp.eval, Bool.and_true]
  have hwit : ∀ i : ℕ, i < n + k →
      (C.gates.foldl PEqualNP.Outside.L_meta_959.wiresStep y).getD i false = w0.getD i false := by
    intro i hi
    rw [hwy]
    rw [PEqualNP.Outside.L_meta_959.getD_foldl_wiresStep _ _ (by
      rw [PEqualNP.Outside.L_meta_959.wiresStep, List.length_append, List.length_singleton, hw0len]
      omega)]
    simpa [PEqualNP.Outside.L_meta_959.wiresStep, GateOp.eval] using
      List.getD_append w0 [w0.getD a false && w0.getD b false] false i (by omega)
  have hbnd : ∀ i : ℕ, w0.getD i false = true → i < n + k := by
    intro i hi
    by_contra hcon
    have hle : w0.length ≤ i := by
      rw [hw0len]
      exact Nat.le_of_not_lt hcon
    have hfalse : w0.getD i false = false := List.getD_eq_default w0 false hle
    rw [hfalse] at hi
    exact Bool.noConfusion hi
  have hunfold : PEqualNP.MetaComplexity.circuitFun n C z =
      (C.gates.foldl PEqualNP.Outside.L_meta_959.wiresStep y).getD (n + k) false := by
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval,
      PEqualNP.Outside.L_meta_959.wires_eq_foldl, hy, hout]
  have hunfold' : ∀ i : ℕ, PEqualNP.MetaComplexity.circuitFun n ⟨C.gates, i⟩ z =
      (C.gates.foldl PEqualNP.Outside.L_meta_959.wiresStep y).getD i false := by
    intro i
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval,
      PEqualNP.Outside.L_meta_959.wires_eq_foldl, hy]
  have hleft : (PEqualNP.MetaComplexity.circuitFun n C z = true) ↔
      (w0.getD a false = true ∧ w0.getD b false = true) := by
    rw [hunfold, hval, Bool.and_eq_true]
  have hA : (a < C.output ∧ PEqualNP.MetaComplexity.circuitFun n ⟨C.gates, a⟩ z = true) ↔
      w0.getD a false = true := by
    constructor
    · intro h
      have ha : a < n + k := by rw [← hout]; exact h.1
      rw [hunfold' a] at h
      exact (hwit a ha).symm.trans h.2
    · intro h
      refine ⟨?_, ?_⟩
      · rw [hout]
        exact hbnd a h
      · rw [hunfold' a, hwit a (hbnd a h)]
        exact h
  have hB : (b < C.output ∧ PEqualNP.MetaComplexity.circuitFun n ⟨C.gates, b⟩ z = true) ↔
      w0.getD b false = true := by
    constructor
    · intro h
      have hb : b < n + k := by rw [← hout]; exact h.1
      rw [hunfold' b] at h
      exact (hwit b hb).symm.trans h.2
    · intro h
      refine ⟨?_, ?_⟩
      · rw [hout]
        exact hbnd b h
      · rw [hunfold' b, hwit b (hbnd b h)]
        exact h
  have hright : ((a < C.output ∧ PEqualNP.MetaComplexity.circuitFun n ⟨C.gates, a⟩ z = true) ∧
      (b < C.output ∧ PEqualNP.MetaComplexity.circuitFun n ⟨C.gates, b⟩ z = true)) ↔
      (w0.getD a false = true ∧ w0.getD b false = true) := by
    rw [hA, hB]
  exact hleft.trans hright.symm
