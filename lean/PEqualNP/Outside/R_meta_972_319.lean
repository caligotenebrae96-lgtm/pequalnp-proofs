import PEqualNP.Defs

set_option maxRecDepth 6500 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_972_319
    (starRepresentation : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26,
        (u.val < 13 ∧ 13 ≤ v.val ∧
            (u.val + (v.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∧ x u = true ∧ x v = true) →
      ∃ stars : List (Fin 26 × List (Fin 26)), (∀ u v : Fin 26, u.val < 13 → 13 ≤ v.val →
          (u.val + (v.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
          ∃ s ∈ stars, s.1 = u ∧ v ∈ s.2 ∨ s.1 = v ∧ u ∈ s.2) ∧ ((stars.map (fun s => s.2.length)).sum + stars.length - 1) ≤ C.size)
    (starCost : ∀ (stars : List (Fin 26 × List (Fin 26))), (∀ u v : Fin 26, u.val < 13 → 13 ≤ v.val →
          (u.val + (v.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
          ∃ s ∈ stars, s.1 = u ∧ v ∈ s.2 ∨ s.1 = v ∧ u ∈ s.2) → 64 ≤ ((stars.map (fun s => s.2.length)).sum + stars.length - 1)) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  intro C hC computes
  have incidence_table : ∀ u v : Fin 26,
      (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ↔ u.val < 13 ∧ 13 ≤ v.val ∧
            (u.val + (v.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
    decide +kernel
  have computes_incidence :
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26,
        (u.val < 13 ∧ 13 ≤ v.val ∧
            (u.val + (v.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∧ x u = true ∧ x v = true := by
    intro x
    rw [computes x]
    constructor
    · rintro ⟨u, v, h, hu, hv⟩
      exact ⟨u, v, (incidence_table u v).mp h, hu, hv⟩
    · rintro ⟨u, v, h, hu, hv⟩
      exact ⟨u, v, (incidence_table u v).mpr h, hu, hv⟩
  obtain ⟨stars, covers, charged⟩ := starRepresentation C hC computes_incidence
  exact (starCost stars covers).trans charged
