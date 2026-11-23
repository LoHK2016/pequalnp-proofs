import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_764

theorem mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (h : HasCircuitSize n f s) (hst : s ≤ t) :
    HasCircuitSize n f t := by
  obtain ⟨C, hC, hsz, hev⟩ := h
  exact ⟨C, hC, le_trans hsz hst, hev⟩

theorem nonconst :
    ∃ y y' : Fin 3 → Bool,
      (fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)) y ≠
        (fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)) y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

theorem sameFun :
    (fun x : Fin 5 → Bool =>
        (x (Fin.castAdd 3 (0 : Fin 2)) && x (Fin.castAdd 3 (1 : Fin 2))) ||
          (fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2))
            (fun j : Fin 3 => x (Fin.natAdd 2 j))) =
      (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) := by
  funext x
  revert x
  decide

theorem transfer {n : ℕ} {f g : (Fin n → Bool) → Bool} (h : f = g) {s : ℕ} :
    HasCircuitSize n f s ↔ HasCircuitSize n g s := by
  rw [h]

theorem splitAt (t : ℕ) :
    HasCircuitSize 5
        (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
        (t + 2) ↔
      4 ≤ t := by
  have h1 :
      HasCircuitSize 5
          (fun x : Fin 5 → Bool =>
            (x (Fin.castAdd 3 (0 : Fin 2)) && x (Fin.castAdd 3 (1 : Fin 2))) ||
              (fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2))
                (fun j : Fin 3 => x (Fin.natAdd 2 j)))
          (t + 2) ↔
        HasCircuitSize 3
          (fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)) t :=
    PEqualNP.MetaComplexity.L153 3 t
      (fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)) nonconst
  exact (transfer sameFun.symm).trans (h1.trans (PEqualNP.MetaComplexity.L100 t))

end PEqualNP.Outside.L_meta_764

theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have hlow :
        ¬ PEqualNP.MetaComplexity.HasCircuitSize 5
            (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s := by
      intro hc
      have hc2 :
          PEqualNP.MetaComplexity.HasCircuitSize 5
            (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4))
            (0 + 2) :=
        PEqualNP.Outside.L_meta_764.mono hc (by omega)
      have h4 : 4 ≤ 0 := (PEqualNP.Outside.L_meta_764.splitAt 0).mp hc2
      omega
    have h6 : ¬ 6 ≤ s := by omega
    exact ⟨fun h => absurd h hlow, fun h => absurd h h6⟩
  · have hsp : s = (s - 2) + 2 := by omega
    rw [hsp, PEqualNP.Outside.L_meta_764.splitAt (s - 2)]
    omega
