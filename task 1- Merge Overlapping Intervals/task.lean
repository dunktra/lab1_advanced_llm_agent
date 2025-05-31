import Std
open Std

/-- Merges a list of integer intervals, combining overlapping intervals.
    Intervals are pairs `(start, end)` with `start ≤ end`. -/
def mergeIntervals (intervals : List (Int × Int)) : List (Int × Int) :=
  -- << CODE START >>
  let sorted := intervals.mergeSort (·.fst ≤ ·.fst)
  let merged :=
    sorted.foldl (fun acc curr =>
      match acc with
      | []       => [curr]
      | h :: t   =>
        if curr.fst ≤ h.snd then
          -- overlap: extend the last interval
          (h.fst, max h.snd curr.snd) :: t
        else
          -- no overlap: append
          curr :: acc)
      []
  merged.reverse
  -- << CODE END >>

/-- Specification: sorted by start and non-overlapping. -/
def mergeIntervals_spec (result : List (Int × Int)) : Prop :=
  -- << SPEC START >>
  -- 1. Result is sorted by `fst`
  result = result.mergeSort (·.fst ≤ ·.fst) ∧
  -- 2. No two adjacent intervals overlap
  result.Pairwise (fun x y => x.snd < y.fst)
  -- << SPEC END >>

--- Test cases
#eval mergeIntervals [(1, 3), (2, 6), (8, 10), (15, 18)]-- Expected: [(1, 6), (8, 10), (15, 18)]
#eval mergeIntervals [(5, 7)]-- Expected: [(5, 7)]
#eval mergeIntervals [(1, 4), (4, 5)]-- Expected: [(1, 5)]
#eval mergeIntervals [(1, 10), (2, 3), (4, 8)]-- Expected: [(1, 10)]
#eval mergeIntervals [(1, 2), (3, 4), (5, 6)]-- Expected: [(1, 2), (3, 4), (5, 6)]
#guard mergeIntervals [(1, 3), (2, 6), (8, 10)] = [(1, 6), (8, 10)]
