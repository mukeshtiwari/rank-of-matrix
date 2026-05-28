import Mathlib.LinearAlgebra.Matrix.Rank

section rank_of_matrix

variable {K : Type _} [Field K]
  [DecidableEq K]

/-
  We invite you to spend between 2 and 4 hours exploring
  this problem. You may wish to define a sparse
  matrix type as part of the exercise. Please note
  that you are not expected to provide a fully
  functional implementation, we just want to learn about
  how you would approach this task.

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
  @sparse_matrix K m n :=
  if hi : i < m then
  if hj : j < m then
    let rows := mx.1
    have hi' : m = rows.size := mx.2.1 ▸ rfl
    have hj' : i < rows.size := mx.2.1 ▸ hi
    have hk' : j < rows.size := mx.2.1 ▸ hj
    let new_rows := rows.swap i j
    ⟨new_rows, by sorry⟩
  else mx
  else mx

/- Multiply a row by a non-zero number. -/
def scale_row {m n : ℕ} (mx : @sparse_matrix K m n) (i : ℕ)
  (c : K) (f : K -> K -> K): @sparse_matrix K m n :=
  if i < m then
    let rows := mx.1
    let new_rows := rows.modify i
      (fun row => row.map (fun p => (p.1, f c p.2)))
    ⟨new_rows, by sorry⟩
  else mx


/-
Combine row i and row j by a linear combination `f`.
It checks if the indices align and then merges the two rows by applying `f` to the values at matching column indices.
-/
def combine_two_rows {m n : ℕ} (mx : @sparse_matrix K m n) (i j : ℕ)
  (f : K → K → K) : @sparse_matrix K m n :=
  if hi : i < m then
  if hj : j < m then
    let rows := mx.1
    have hi' : i < rows.size := mx.2.1 ▸ hi
    have hj' : j < rows.size := mx.2.1 ▸ hj
    let row_i := rows[i]'hi'
    let row_j := rows[j]'hj'
    let new_row := row_i.zipWith
      (fun x y => if x.1 = y.1 then (x.1, f x.2 y.2)
        else if x.1 < y.1 then (x.1, f x.2 0)
        else (y.1, f 0 y.2)) row_j
    let new_rows := rows.set i new_row hi'
    ⟨new_rows, by sorry⟩
  else mx
  else mx

/-
Perform Gaussian elimination to convert the matrix to
Row Echelon Form (REF). Returns the REF matrix and the rank.
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
