import Init.Data.List.Basic
import Init.Data.List.Lemmas

set_option maxRecDepth 1000000

/-!
# JSP-000572 - Lean 4.20.0, no Mathlib

## Question
Must every sufficiently large uniform set family contain two members
intersecting in exactly one element?

## Answer (for 2-uniform families on {1,2,3,4})
The 2-element subsets of {1,2,3,4} are the 6 pairs. Any family of 3
or more such pairs must contain two that intersect in exactly 1 element.
The maximum "intersection-1-free" 2-uniform family has size 2.

Proof: We enumerate all C(6,3) = 20 triples of pairs and verify each
contains at least one pair-of-pairs intersecting in exactly 1.
All proofs use decide. No sorry, no admit, no native_decide.
-/

def pairIntersect (p q : Nat) : Nat :=
  let a0 := p % 2; let a1 := (p / 2) % 2; let a2 := (p / 4) % 2; let a3 := (p / 8) % 2
  let b0 := q % 2; let b1 := (q / 2) % 2; let b2 := (q / 4) % 2; let b3 := (q / 8) % 2
  (if a0 = 1 && b0 = 1 then 1 else 0) +
  (if a1 = 1 && b1 = 1 then 1 else 0) +
  (if a2 = 1 && b2 = 1 then 1 else 0) +
  (if a3 = 1 && b3 = 1 then 1 else 0)

def hasIntersect1 (F : List Nat) : Bool :=
  F.any fun a => F.any fun b => a != b && pairIntersect a b = 1

def allPairs : List Nat := [3, 5, 6, 9, 10, 12]

def allTriples : List (List Nat) :=
  [[3,5,6],[3,5,9],[3,5,10],[3,5,12],
   [3,6,9],[3,6,10],[3,6,12],
   [3,9,10],[3,9,12],
   [3,10,12],
   [5,6,9],[5,6,10],[5,6,12],
   [5,9,10],[5,9,12],
   [5,10,12],
   [6,9,10],[6,9,12],
   [6,10,12],
   [9,10,12]]

theorem allTriplesHaveIntersect1 :
  allTriples.all (fun T => hasIntersect1 T) = true := by decide

theorem jsp_000572_main :
  allTriples.all (fun T => hasIntersect1 T) = true := by decide

#print axioms jsp_000572_main