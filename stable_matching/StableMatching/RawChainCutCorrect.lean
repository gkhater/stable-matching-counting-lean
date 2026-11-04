import StableMatching.RawChainCut

/-! Exact serialization of the executable raw clauses. -/

namespace StableMatching.RawChainCut

private theorem map_product {α β γ δ : Type*} (xs : List α) (ys : List β)
    (f : α → γ) (g : β → δ) :
    (xs.map f) ×ˢ (ys.map g) =
      (xs ×ˢ ys).map (fun p => (f p.1, g p.2)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.product_cons, ih, List.map_map, Function.comp_def]

theorem entries_eq_allEntries {b ℓ : Nat} (blocks : Blocks)
    (hblocks : blocks.length = b) :
    entries blocks (List.range (2 ^ ℓ)) =
      (BinaryCSP.allEntries b ℓ).map (fun p => (p.1.val, p.2.val)) := by
  unfold entries BinaryCSP.allEntries
  rw [hblocks, range_eq_map_finRange b, range_eq_map_finRange (2 ^ ℓ)]
  change ((List.finRange b).map Fin.val) ×ˢ
      ((List.finRange (2 ^ ℓ)).map Fin.val) = _
  exact map_product _ _ _ _

theorem invalidEntries_eq {b ℓ : Nat} (s : BinaryCSP.Spec b ℓ)
    (blocks : Blocks) (hblocks : blocks.length = b)
    (hvalid : ∀ (i : Fin b) (v : Fin (2 ^ ℓ)),
      decide (v.val > (blocks.getD i.val []).length) =
        decide (s.validTest i v = false)) :
    invalidEntries blocks (List.range (2 ^ ℓ)) =
      (BinaryCSP.invalidEntries s).map (fun p => (p.1.val, p.2.val)) := by
  unfold invalidEntries BinaryCSP.invalidEntries
  rw [entries_eq_allEntries blocks hblocks, List.filter_map]
  simp only [Function.comp_def]
  congr 1
  congr 1
  funext p
  exact hvalid p.1 p.2

theorem badPairEntries_eq {b ℓ : Nat} (s : BinaryCSP.Spec b ℓ)
    (blocks : Blocks) (matrix : Matrix) (hblocks : blocks.length = b)
    (hcompatible : ∀ (i j : Fin b) (u v : Fin (2 ^ ℓ)),
      compatible blocks matrix i.val j.val u.val v.val =
        s.compatibleTest i j u v) :
    badPairEntries blocks matrix (List.range (2 ^ ℓ)) =
      (BinaryCSP.badPairEntries s).map (fun p =>
        ((p.1.1.val, p.1.2.val), (p.2.1.val, p.2.2.val))) := by
  unfold badPairEntries BinaryCSP.badPairEntries
  rw [entries_eq_allEntries blocks hblocks]
  change (((BinaryCSP.allEntries b ℓ).map (fun p => (p.1.val, p.2.val))) ×ˢ
      ((BinaryCSP.allEntries b ℓ).map (fun p => (p.1.val, p.2.val)))).filter _ = _
  rw [map_product, List.filter_map]
  simp only [Function.comp_def]
  congr 1
  congr 1
  funext p
  rw [hcompatible]
  cases s.compatibleTest p.1.1 p.2.1 p.1.2 p.2.2 <;> rfl

/-- Replace each bounded variable index by its natural-number value. -/
def serialize (φ : StableMatching.CNF) : RawCNF :=
  (φ.numVars, φ.clauses.map (fun clause => clause.map (fun lit => (lit.1.val, lit.2))))

theorem encode_eq_serialize_spec {b ℓ : Nat} (s : BinaryCSP.Spec b ℓ)
    (blocks : Blocks) (matrix : Matrix) (domain : List Nat) (fuel : List Unit)
    (hblocks : blocks.length = b) (hdomain : domain = List.range (2 ^ ℓ))
    (hlen : fuel.length = ℓ)
    (hvalid : ∀ (i : Fin b) (v : Fin (2 ^ ℓ)),
      decide (v.val > (blocks.getD i.val []).length) =
        decide (s.validTest i v = false))
    (hcompatible : ∀ (i j : Fin b) (u v : Fin (2 ^ ℓ)),
      compatible blocks matrix i.val j.val u.val v.val =
        s.compatibleTest i j u v) :
    encode blocks matrix domain fuel = serialize (BinaryCSP.cnf s) := by
  subst domain
  have hu :
      (invalidEntries blocks (List.range (2 ^ ℓ))).map
          (fun p => forbid fuel p.1 p.2) =
        (BinaryCSP.invalidEntries s).map (fun p =>
          (BinaryCSP.forbid p.1 p.2).map (fun lit => (lit.1.val, lit.2))) := by
    rw [invalidEntries_eq s blocks hblocks hvalid, List.map_map]
    congr 1
    funext p
    exact forbid_eq_generic fuel hlen p.1 p.2
  have hb :
      (badPairEntries blocks matrix (List.range (2 ^ ℓ))).map
          (fun p => forbid fuel p.1.1 p.1.2 ++ forbid fuel p.2.1 p.2.2) =
        (BinaryCSP.badPairEntries s).map (fun p =>
          (BinaryCSP.forbid p.1.1 p.1.2 ++ BinaryCSP.forbid p.2.1 p.2.2).map
            (fun lit => (lit.1.val, lit.2))) := by
    rw [badPairEntries_eq s blocks matrix hblocks hcompatible, List.map_map]
    congr 1
    funext p
    simp only [Function.comp_def]
    rw [forbid_eq_generic fuel hlen p.1.1 p.1.2,
      forbid_eq_generic fuel hlen p.2.1 p.2.2, List.map_append]
  unfold encode serialize BinaryCSP.cnf
  simp only [hblocks, hlen, hu, hb, List.map_append, List.map_map, Function.comp_def]

section BlockBridge

variable {P : Type*} [PartialOrder P] [DecidableEq P] {D : Nat}

/-- The numeric block representation expected by the raw constructor. -/
def blocksOf (d : BlockPartition.Data P D) (vertex : P → Nat) : Blocks :=
  d.blocks.map (fun block => block.map vertex)

@[simp] theorem blocksOf_length (d : BlockPartition.Data P D) (vertex : P → Nat) :
    (blocksOf d vertex).length = d.blocks.length := by simp [blocksOf]

theorem blocksOf_getD (d : BlockPartition.Data P D) (vertex : P → Nat)
    (i : Fin d.blocks.length) :
    (blocksOf d vertex).getD i.val [] = (d.blocks.get i).map vertex := by
  unfold blocksOf
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem blocksOf_entry (d : BlockPartition.Data P D) (vertex : P → Nat)
    (i : Fin d.blocks.length) (r : Fin (d.blocks.get i).length) :
    ((blocksOf d vertex).getD i.val []).getD r.val 0 =
      vertex ((d.blocks.get i).get r) := by
  rw [blocksOf_getD]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

variable [DecidableLE P]

omit [DecidableLE P] in
theorem compatible_iff_blocks (d : BlockPartition.Data P D)
    (vertex : P → Nat) (matrix : Matrix)
    (hmat : ∀ x y : P, matrixAt matrix (vertex x) (vertex y) = true ↔ x ≤ y)
    {ℓ : Nat} (i j : Fin d.blocks.length) (u v : Fin (2 ^ ℓ)) :
    compatible (blocksOf d vertex) matrix i.val j.val u.val v.val = true ↔
      ∀ (r : Fin (d.blocks.get i).length) (t : Fin (d.blocks.get j).length),
        (d.blocks.get i).get r ≤ (d.blocks.get j).get t →
          t.val < v.val → r.val < u.val := by
  rw [compatible_eq_true_iff]
  constructor
  · intro h r t hle ht
    have hi : r.val < ((blocksOf d vertex).getD i.val []).length := by
      rw [blocksOf_getD, List.length_map]
      exact r.isLt
    have hj : t.val < ((blocksOf d vertex).getD j.val []).length := by
      rw [blocksOf_getD, List.length_map]
      exact t.isLt
    apply h r.val hi t.val hj
    · rw [blocksOf_entry, blocksOf_entry]
      exact (hmat _ _).mpr hle
    · exact ht
  · intro h r hr t ht hrel hcut
    let rr : Fin (d.blocks.get i).length := ⟨r, by
      rw [blocksOf_getD, List.length_map] at hr
      exact hr⟩
    let tt : Fin (d.blocks.get j).length := ⟨t, by
      rw [blocksOf_getD, List.length_map] at ht
      exact ht⟩
    have hle : (d.blocks.get i).get rr ≤ (d.blocks.get j).get tt := by
      apply (hmat _ _).mp
      rw [← blocksOf_entry d vertex i rr, ← blocksOf_entry d vertex j tt]
      exact hrel
    exact h rr tt hle hcut

omit [DecidableLE P] in
theorem chainPosition_le_iff (d : BlockPartition.Data P D)
    (i j : Fin d.blocks.length)
    (r : Fin (d.blocks.get i).length) (t : Fin (d.blocks.get j).length) :
    d.labelEquiv.symm ⟨i, r⟩ ≤
        d.labelEquiv.symm ⟨j, t⟩ ↔
      (d.blocks.get i).get r ≤ (d.blocks.get j).get t := by
  rw [d.labelEquiv_symm_apply, d.labelEquiv_symm_apply]
  rfl

theorem compatible_eq_spec (d : BlockPartition.Data P D)
    (vertex : P → Nat) (matrix : Matrix)
    (hmat : ∀ x y : P, matrixAt matrix (vertex x) (vertex y) = true ↔ x ≤ y)
    {ℓ : Nat} (i j : Fin d.blocks.length) (u v : Fin (2 ^ ℓ)) :
    compatible (blocksOf d vertex) matrix i.val j.val u.val v.val =
      (d.chainPartition.spec (ℓ := ℓ)).compatibleTest i j u v := by
  letI : Decidable ((d.chainPartition.spec (ℓ := ℓ)).compatible i j u v) :=
    (d.chainPartition.spec (ℓ := ℓ)).compatibleDecide i j u v
  apply Bool.eq_iff_iff.mpr
  rw [compatible_iff_blocks d vertex matrix hmat i j u v]
  rw [BinaryCSP.Spec.compatibleTest, decide_eq_true_eq]
  change (∀ r t, (d.blocks.get i).get r ≤ (d.blocks.get j).get t →
      t.val < v.val → r.val < u.val) ↔
    (∀ r t, d.labelEquiv.symm ⟨i, r⟩ ≤
      d.labelEquiv.symm ⟨j, t⟩ → t.val < v.val → r.val < u.val)
  simp only [chainPosition_le_iff]

theorem invalid_eq_spec (d : BlockPartition.Data P D)
    (vertex : P → Nat) {ℓ : Nat}
    (i : Fin d.blocks.length) (v : Fin (2 ^ ℓ)) :
    decide (v.val > ((blocksOf d vertex).getD i.val []).length) =
      decide ((d.chainPartition.spec (ℓ := ℓ)).validTest i v = false) := by
  rw [blocksOf_getD, List.length_map]
  change decide (v.val > (d.blocks.get i).length) =
    decide (decide (v.val ≤ (d.blocks.get i).length) = false)
  simp

/-- The executable clauses are byte-for-byte the natural-index serialization
of the previously verified compact lower-set encoder. -/
theorem encode_eq_blockPartition (d : BlockPartition.Data P D)
    (vertex : P → Nat) (matrix : Matrix)
    (hmat : ∀ x y : P, matrixAt matrix (vertex x) (vertex y) = true ↔ x ≤ y)
    (ℓ : Nat) (fuel : List Unit) (hlen : fuel.length = ℓ) :
    encode (blocksOf d vertex) matrix (List.range (2 ^ ℓ)) fuel =
      serialize (d.encode ℓ) := by
  change encode (blocksOf d vertex) matrix (List.range (2 ^ ℓ)) fuel =
    serialize (BinaryCSP.cnf (d.chainPartition.spec (ℓ := ℓ)))
  exact encode_eq_serialize_spec _ _ _ _ _ (blocksOf_length d vertex) rfl hlen
    (invalid_eq_spec d vertex) (compatible_eq_spec d vertex matrix hmat)

theorem encode_correct (d : BlockPartition.Data P D)
    (vertex : P → Nat) (matrix : Matrix)
    (hmat : ∀ x y : P, matrixAt matrix (vertex x) (vertex y) = true ↔ x ≤ y)
    (ℓ : Nat) (fuel : List Unit) (hlen : fuel.length = ℓ)
    (hcap : D + 1 ≤ 2 ^ ℓ) :
    ∃ φ : StableMatching.CNF,
      encode (blocksOf d vertex) matrix (List.range (2 ^ ℓ)) fuel = serialize φ ∧
      φ.satCount = Nat.card (LowerSet {x : P // x ∈ d.remaining}) := by
  exact ⟨d.encode ℓ, encode_eq_blockPartition d vertex matrix hmat ℓ fuel hlen,
    d.encode_correct hcap⟩


end BlockBridge

end StableMatching.RawChainCut
