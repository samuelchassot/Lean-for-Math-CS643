/-
  The theorem should be proven/defined by directly applying the recursor
  (BinTree.rec or Subtree.rec) as a term, making the induction principle
  fully explicit. The `induction` tactic should not be used.


  The general shape of every proof is:
    theorem foo (t : BinTree) : P t :=
      BinTree.rec
        (motive := fun t => P t)   -- declare what property is being proved
        <base case proof>          -- prove P leaf
        (fun l r ihl ihr => ...)   -- prove P (node l r) using ihl : P l and ihr : P r
        t                          -- apply the recursor to the specific tree t

-/


inductive BinTree : Type where          -- declares a new inductive type living in Type (not Prop)
  | leaf : BinTree                      -- base case: a single vertex with no children
  | node : BinTree → BinTree → BinTree  -- recursive case: a root with a left AND right subtree

/-
  Compare with Nat:

    inductive Nat : Type where
      | zero : Nat
      | succ : Nat → Nat          -- ONE recursive argument

  BinTree replaces `succ` with `node`, which takes two recursive arguments.
-/


open BinTree  -- brings leaf and node into scope so we can write `leaf` instead of `BinTree.leaf`

def t0 : BinTree := leaf
def t1 : BinTree := node leaf leaf
def t2 : BinTree := node (node leaf leaf) leaf
def t3 : BinTree := node leaf (node leaf leaf)
def t4 : BinTree := node (node leaf leaf) (node leaf leaf)

/-
  Lean auto-generates BinTree.rec with the following signature:

    BinTree.rec :
      {motive : BinTree → Sort u}           -- the property P to be proved or computed
      → motive leaf                         -- proof/value for the base case P(leaf)
      → (∀ l r, motive l → motive r         -- proof/value for the step:
                          → motive (node l r))  -- given P(l) and P(r), produce P(node l r)
      → ∀ (t : BinTree), motive t           -- conclusion: P holds for every tree t

  The two arguments `motive l` and `motive r` in the step are the
  two independent inductive hypotheses: one per subtree.

  This is structural induction on trees: the recursor IS that principle.
  Every proof below is literally an application of this term.
-/

def numNodes (t : BinTree) : Nat := -- by sorry
  match t with
  | leaf     => 0
  | node l r => numNodes l + numNodes r + 1

def numLeaves (t : BinTree) : Nat :=  -- by sorry
  match t with
  | leaf     => 1
  | node l r => numLeaves l + numLeaves r

/- Exercise **

  Theorem: For any full binary tree t,
              numLeaves t = numNodes t + 1

 Note: Replace the current proof with a manual proof term as an application of
 BinTree.rec.

 The goal is for you to get familiar with the recursor and how to use it, and to
 see the inductive structure of trees and the usage of proofs of equality.

 Feel free to use the theorem/definition:
 - [Eq.trans] already proven in Lean [Eq.trans : (h₁ : a = b) (h₂ : b = c) : a = c]
 - [Nat.add_succ] already proven  during the second hour of lecture, and that also exists in Lean standard library: [Nat.add_succ : add (succ n) m = succ (add n m)]
 - [Nat.succ_add] already proven during the second hour of lecture, and that also exists in Lean standard library: [Nat.succ_add : add n (succ m) = succ (add n m)]
 -/

theorem leaves_eq_nodes_succ (t : BinTree) : numLeaves t = numNodes t + 1 := -- Delete the proof below
 by
  induction t
  . simp [numLeaves, numNodes]
  . simp [numLeaves, numNodes]
    grind
