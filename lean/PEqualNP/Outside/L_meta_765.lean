import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_765

theorem mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (h : HasCircuitSize n f s) (hst : s ≤ t) :
    HasCircuitSize n f t := by
  obtain ⟨C, hC, hsz, hev⟩ := h
  exact ⟨C, hC, le_trans hsz hst, hev⟩

theorem nonconst :
    ∃ y y' : Fin 4 → Bool,
      (fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)) y ≠ (fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)) y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

theorem sameFun :
    (fun x : Fin 6 → Bool =>
        (x (Fin.castAdd 4 (0 : Fin 2)) && x (Fin.castAdd 4 (1 : Fin 2))) ||
          (fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0))
            (fun j : Fin 4 => x (Fin.natAdd 2 j))) =
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) := by
  funext x
  revert x
  decide

theorem transfer {n : ℕ} {f g : (Fin n → Bool) → Bool} (h : f = g) {s : ℕ} :
    HasCircuitSize n f s ↔ HasCircuitSize n g s := by
  rw [h]

theorem splitAt (t : ℕ) :
    HasCircuitSize 6
        (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2))
        (t + 2) ↔
      3 ≤ t := by
  have h1 :
      HasCircuitSize 6
          (fun x : Fin 6 → Bool =>
            (x (Fin.castAdd 4 (0 : Fin 2)) && x (Fin.castAdd 4 (1 : Fin 2))) ||
              (fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0))
                (fun j : Fin 4 => x (Fin.natAdd 2 j)))
          (t + 2) ↔
        HasCircuitSize 4 (fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)) t :=
    PEqualNP.MetaComplexity.L153 4 t (fun y : Fin 4 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)) nonconst
  exact (transfer sameFun.symm).trans (h1.trans (PEqualNP.MetaComplexity.L112 t))

end PEqualNP.Outside.L_meta_765

theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s := by
  intro s
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have hlow :
        ¬ PEqualNP.MetaComplexity.HasCircuitSize 6
            (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s := by
      intro hc
      have hc2 :
          PEqualNP.MetaComplexity.HasCircuitSize 6
            (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2))
            (0 + 2) :=
        PEqualNP.Outside.L_meta_765.mono hc (by omega)
      have h3 : 3 ≤ 0 := (PEqualNP.Outside.L_meta_765.splitAt 0).mp hc2
      omega
    have h5 : ¬ 5 ≤ s := by omega
    exact ⟨fun h => absurd h hlow, fun h => absurd h h5⟩
  · have hsp : s = (s - 2) + 2 := by omega
    rw [hsp, PEqualNP.Outside.L_meta_765.splitAt (s - 2)]
    omega
