import Mathlib.LinearAlgebra.Matrix.Rank

section rank_of_matrix

variable {K : Type _} [Field K]
  [DecidableEq K]

/-
  Datastructure for sparse matrix: a sigma type in which we
  store a list of rows, where each row is
  a list of pairs (column index, value). We only store
  non-zero entries for
  efficiency and colum indices are increasing
  in each row. For computation, it does not matter
  but it will matter during proof.

  #print List.Pairwise

  def sparse_matrix (m n : ℕ) :=
  { rows : List (List (ℕ × K)) //
    rows.length = m ∧
    ∀ row ∈ rows, (∀ p ∈ row, p.1 < n) ∧
      row.Pairwise (fun a b => a.1 < b.1) }

  The problem with previous representation is that it is
    O(n) so we can turn the outside representation into Array
    for O(1) access, but we still have O(n) access for each row.
-/

def sparse_matrix (m n : ℕ) :=
  { rows : Array (List (ℕ × K)) //
    rows.size = m ∧
    ∀ row ∈ rows, (∀ p ∈ row, p.1 < n) ∧
      row.Pairwise (fun a b => a.1 < b.1) }

/-
Swap two rows. Do we need to assume that i and j are less than m?
We can just return the original matrix if they are not.
Fill the proofs using refine tactic?
-/


def swap_rows {m n : ℕ} (mx : @sparse_matrix K m n) (i j : ℕ) :
  @sparse_matrix K m n := by
  refine(
  if hi : i < m then
  if hj : j < m then
    let rows := mx.1
    have hi' : m = rows.size := mx.2.1 ▸ rfl
    have hj' : i < rows.size := mx.2.1 ▸ hi
    have hk' : j < rows.size := mx.2.1 ▸ hj
    let new_rows := rows.swap i j
    ⟨new_rows, ?_⟩
  else mx
  else mx)
  refine(And.intro ?_ ?_)
  · rcases mx with ⟨mxh, ⟨hf, hs⟩⟩
    subst hf
    eapply Array.size_swap
  · intro row hr
    rcases mx with ⟨mxh, ⟨hfa, hsa⟩⟩
    subst hfa new_rows rows
    have hperm : (row ∈ mxh <-> row ∈ mxh.swap i j hi hj) :=
      Array.Perm.mem_iff (Array.Perm.symm (Array.swap_perm _ _))
    have hr_mxh : row ∈ mxh := by
      exact hperm.mpr hr
    specialize hsa row hr_mxh
    refine(And.intro ?_ ?_)
    · intro p hp
      exact hsa.1 p hp
    · exact hsa.2


/- This should exists somewhere in the library -/
lemma mem_or_exists_map_of_mem_modify
  {i : ℕ} {c : K} {f : K -> K -> K}
  {row : List (ℕ × K)} {mxh : Array (List (ℕ × K))}
  (hr : row ∈ mxh.modify i (fun row => row.map (fun p => (p.1, f c p.2)))) :
  row ∈ mxh ∨ ∃ r, r ∈ mxh ∧ row = r.map (fun q => (q.1, f c q.2)) := by
  rcases (Array.mem_iff_getElem.mp hr) with ⟨k, hk, hkrow⟩
  have hk' : k < mxh.size := by
    simpa [Array.size_modify] using hk
  by_cases hki : i = k
  · right
    refine ⟨mxh[k], ?_, ?_⟩
    · exact Array.mem_iff_getElem.mpr ⟨k, hk', rfl⟩
    · have hget :
        (mxh.modify i (fun row => row.map (fun p => (p.1, f c p.2))))[k] =
          (if i = k then (mxh[k]).map (fun p => (p.1, f c p.2)) else mxh[k]) := by
          rw [Array.getElem_modify]
      calc
        row = (mxh.modify i (fun row => row.map (fun p => (p.1, f c p.2))))[k] := hkrow.symm
        _ = (if i = k then (mxh[k]).map (fun p => (p.1, f c p.2)) else mxh[k]) := hget
        _ = (mxh[k]).map (fun p => (p.1, f c p.2)) := by simp [hki]
  · left
    have hget :
        (mxh.modify i (fun row => row.map (fun p => (p.1, f c p.2))))[k] =
          (if i = k then (mxh[k]).map (fun p => (p.1, f c p.2)) else mxh[k]) := by
          rw [Array.getElem_modify]
    have : row = mxh[k] := by
      calc
        row = (mxh.modify i (fun row => row.map (fun p => (p.1, f c p.2))))[k] := hkrow.symm
        _ = (if i = k then (mxh[k]).map (fun p => (p.1, f c p.2)) else mxh[k]) := hget
        _ = mxh[k] := by simp [hki]
    exact Array.mem_iff_getElem.mpr ⟨k, hk', this.symm⟩



def scale_row {m n : ℕ} (mx : @sparse_matrix K m n) (i : ℕ)
  (c : K) (f : K -> K -> K) : @sparse_matrix K m n := by
  refine(
  if i < m then
    let rows := mx.1
    let new_rows := rows.modify i
      (fun row => row.map (fun p => (p.1, f c p.2)))
    ⟨new_rows, ?_⟩
  else mx)
  refine(And.intro ?_ ?_)
  · rcases mx with ⟨mxh, ⟨hf, hs⟩⟩
    subst hf
    unfold new_rows
    eapply Array.size_modify
  · intro row hr
    rcases mx with ⟨mxh, ⟨hfa, hsa⟩⟩
    subst hfa new_rows rows
    simp at hr
    have hmod :
      row ∈ mxh ∨ ∃ r, r ∈ mxh ∧ row = r.map
      (fun q => (q.1, f c q.2)) := by
      exact mem_or_exists_map_of_mem_modify hr
    refine(And.intro ?_ ?_)
    · intro p hp
      rcases hmod with hrow | ⟨r, hrmem, rfl⟩
      · exact (hsa row hrow).1 p hp
      · rcases List.mem_map.mp hp with ⟨q, hq, hpeq⟩
        have hq₁ : q.1 < n := (hsa r hrmem).1 q hq
        rcases p with ⟨pa, pb⟩
        simp; simp at hpeq
        rcases hpeq with ⟨hpeq₁, hpeq₂⟩
        rw [<-hpeq₁]
        exact hq₁
    · rcases hmod with hrow | ⟨r, hrmem, rfl⟩
      · exact (hsa row hrow).2
      · exact List.Pairwise.map
          (f := fun q : ℕ × K => (q.1, f c q.2))
          (R := fun a b : ℕ × K => a.1 < b.1)
          (S := fun a b : ℕ × K => a.1 < b.1)
          (H := by
            intro a b hab
            simpa using hab)
          ((hsa r hrmem).2)



/- Library function for this? -/
def merge_rows (f : K → K → K) (xs ys : List (ℕ × K)) : List (ℕ × K) :=
  match xs, ys with
  | [], ys => List.map (fun p => (p.1, f 0 p.2)) ys
  | xs, [] => List.map (fun p => (p.1, f p.2 0)) xs
  | (x1, x2) :: xs', (y1, y2) :: ys' =>
      if x1 = y1 then
        (x1, f x2 y2) :: merge_rows f xs' ys'
      else if x1 < y1 then
        (x1, f x2 0) :: merge_rows f xs' ((y1, y2) :: ys')
      else
        (y1, f 0 y2) :: merge_rows f ((x1, x2) :: xs') ys'
  termination_by xs.length + ys.length


/-
Combine row i and row j by a linear combination `f`.
It checks if the indices align and then merges the two rows by applying `f` to the values at matching column indices.
-/
def combine_two_rows {m n : ℕ} (mx : @sparse_matrix K m n) (i j : ℕ)
  (f : K → K → K) : @sparse_matrix K m n := by
  refine(
  if hi : i < m then
  if hj : j < m then
    let rows := mx.1
    have hi' : i < rows.size := mx.2.1 ▸ hi
    have hj' : j < rows.size := mx.2.1 ▸ hj
    let row_i := rows[i]'hi'
    let row_j := rows[j]'hj'
    let new_row := merge_rows f row_i row_j
    let new_rows := rows.set i new_row hi'
    ⟨new_rows, ?_⟩
  else mx
  else mx)
  refine(And.intro ?_ ?_)
  · rcases mx with ⟨mxh, ⟨hf, hs⟩⟩
    subst hf
    eapply Array.size_set
  · intro row hr
    rcases mx with ⟨mxh, ⟨hfa, hsa⟩⟩
    refine(And.intro ?_ ?_)
    · intro p hp
      unfold new_rows at hr
      have hrow : row ∈ rows ∨ row = new_row := Array.mem_or_eq_of_mem_set hr
      rcases hrow with hrow_old | rfl
      · exact (hsa row hrow_old).1 p hp
      · rcases List.mem_iff_getElem.mp hp with ⟨k, hk, hk_eq⟩
        sorry
    · sorry




/-
Perform Gaussian elimination to convert the matrix to
Row Echelon Form (REF). Returns the REF matrix .
-/
def gaussian_elimination {m n : ℕ} (mx : @sparse_matrix K m n) :
    @sparse_matrix K m n :=
  sorry

/- count number of non-zero rows in A -/
def count_non_zero_rows {m n : ℕ} (mx : @sparse_matrix K m n) : ℕ :=
  mx.1.foldl (fun acc row => if row.isEmpty then acc else acc + 1) 0


/-
The rank of a sparse matrix: the number of non-zero rows
after Gaussian elimination.
-/
def computable_rank {m n : ℕ} (mx : @sparse_matrix K m n) : ℕ :=
  count_non_zero_rows (gaussian_elimination mx)


/-
Now I need to prove that the computable rank is equal to the
Mathlib rank definition.
-/
def sparse_matrix_to_matrix {m n : ℕ} (mx : @sparse_matrix K m n) :
  Matrix (Fin m) (Fin n) K :=
  fun i j =>
    have hi : (i : ℕ) < mx.1.size := by
      rw [mx.2.1]
      exact i.2
    let row := mx.1[i]'hi
    match row.find? (fun p => p.1 = j.1) with
    | some p => p.2
    | none => 0

/-
Main correctness theorem: the algorithmic rank on sparse matrices
agrees with Mathlib's rank on the corresponding dense matrix.
-/
theorem computable_rank_correct {m n : ℕ} (A : @sparse_matrix K m n) :
  computable_rank A = Matrix.rank (sparse_matrix_to_matrix A) := by
  sorry



end rank_of_matrix
/-
time right now: 12:19
-/
