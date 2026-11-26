import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

theorem PEqualNP.Outside.L_meta_17887 : (∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : SimpleGraph (Fin (x1 + x2))), (∀ (x6 x7 : Fin (x1 + x2)), x5.Adj x6 x7 ↔ ∃ x8 ∈ x3, x6 = Fin.castAdd x2 x8.1 ∧ x7 = Fin.natAdd x1 x8.2 ∨ x7 = Fin.castAdd x2 x8.1 ∧ x6 = Fin.natAdd x1 x8.2) → ¬x5.IsAcyclic → (∀ x8 ∈ x4, ∀ x10 ∈ x4, x8.1 = x10.1 → x8 = x10) → (∀ x9 ∈ x4, ∀ x11 ∈ x4, x9.2 = x11.2 → x9 = x11) → x4 ⊆ x3 → (∀ (x11 x12 : Fin x1) (x13 x14 : Fin x2), x11 ≠ x12 → x13 ≠ x14 → ¬((x11, x13) ∈ x3 ∧ (x11, x14) ∈ x3 ∧ (x12, x13) ∈ x3 ∧ (x12, x14) ∈ x3)) → (∀ x12 ∈ x3, ((∀ x14 ∈ x3, x14.1 = x12.1 → x14 = x12) ∨ ∀ x14 ∈ x3, x14.2 = x12.2 → x14 = x12) → (x3.erase x12).Nonempty → x12 ∈ x4) → ∃ x13 ∈ x3, x13 ∉ x4) := by
  intro m n E M G adj cyc left right _ _ _
  by_contra h
  have incl : ∀ e ∈ E, e ∈ M := by
    intro e he
    by_contra hn
    exact h ⟨e,he,hn⟩
  have cross (a : Fin m) (b : Fin n) : Fin.castAdd n a ≠ Fin.natAdd m b := by
    intro eq
    have v := congrArg Fin.val eq
    change a.val = m + b.val at v
    omega
  have unique {u v w : Fin (m+n)} (hu : G.Adj u v) (hw : G.Adj u w) : v = w := by
    obtain ⟨e,he,hor⟩ := (adj _ _).mp hu
    obtain ⟨f,hf,hs⟩ := (adj _ _).mp hw
    rcases hor with ⟨eu,ev⟩ | ⟨ev,eu⟩ <;> rcases hs with ⟨fu,fw⟩ | ⟨fw,fu⟩
    · have eq : e = f := left e (incl e he) f (incl f hf) (Fin.castAdd_inj.mp (eu.symm.trans fu))
      exact ev.trans ((congrArg (fun z : Fin m × Fin n => Fin.natAdd m z.2) eq).trans fw.symm)
    · exact (cross _ _ (eu.symm.trans fu)).elim
    · exact (cross _ _ (fu.symm.trans eu)).elim
    · have d := congrArg Fin.val (eu.symm.trans fu)
      change m + e.2.val = m + f.2.val at d
      have eq : e = f := right e (incl e he) f (incl f hf) (Fin.ext (by omega))
      exact ev.trans ((congrArg (fun z : Fin m × Fin n => Fin.castAdd n z.1) eq).trans fw.symm)
  apply cyc
  intro u p hp
  have hl := hp.three_le_length
  have vw := unique (p.adj_getVert_succ (i := 0) (by omega)).symm
    (p.adj_getVert_succ (i := 1) (by omega))
  have impossible : (0 : ℕ) = 2 := hp.getVert_injOn'
    (by change 0 ≤ p.length - 1; omega) (by change 2 ≤ p.length - 1; omega) vw
  omega
