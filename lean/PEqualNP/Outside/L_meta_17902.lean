import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17902 : ∀ (x1 x2 x3 : (Fin (10 : ℕ) → Bool) → Bool), (∀ (x4 : Fin (10 : ℕ) → Bool), x1 x4 = Bool.false → x2 x4 = Bool.false ∧ x3 x4 = Bool.false) → (¬∃ (x5 : Fin (10 : ℕ) → Bool), x1 x5 = Bool.true ∧ x2 x5 = Bool.false ∧ x3 x5 = Bool.false) → ∀ (x6 : Fin (10 : ℕ) → Bool), x1 x6 = (x2 x6 || x3 x6) := by
  intro f g h h0 hn x
  cases hf : f x
  · obtain ⟨a, b⟩ := h0 x hf
    rw [a, b]; rfl
  · cases hg : g x
    · cases hh : h x
      · exact absurd ⟨x, hf, hg, hh⟩ hn
      · rfl
    · rfl
