/-
  Formal Mathematics with Lean and AI: Lecture 3
  Companion Lean 4 file

  Topics:
  1. Disjunction (Or) as an inductive type
  2. Natural numbers, recursion principle, pattern matching
  3. Defining addition
  4. Equality: Leibniz equality and inductive equality
  5. Proof by induction: add n 0 = n

  We use `#print` and `#check` extensively to inspect the lambda terms
  that Lean generates for our definitions and proofs.
-/

-- ============================================================
-- PART 1: DISJUNCTION
-- ============================================================

/-
  Disjunction (Or) is already defined in Lean's core library.
  Let's look at how it's defined:
-/

#print Or
-- inductive Or (a b : Prop) : Prop where
--   | inl : a → Or a b
--   | inr : b → Or a b
-- (Note: typing fancy symbols in Lean is easy: \to to get → , \forall to get ∀, etc...)

-- The elimination principle (recursor) is generated automatically:
#check @Or.rec
-- Or.rec : {a b : Prop} → {motive : Or a b → Prop} →
--          (∀ h : a, motive (Or.inl h)) →
--          (∀ h : b, motive (Or.inr h)) →
--          ∀ t : Or a b, motive t

/-
  Example: prove A ∨ B → B ∨ A (commutativity of Or).
  We do case analysis: if we got inl (a proof of A), we produce inr;
  if we got inr (a proof of B), we produce inl.
-/


-- Term-mode proof (explicit lambda terms):
theorem or_comm_term (A B : Prop) : A ∨ B → B ∨ A :=
  fun h => Or.elim h (fun ha => Or.inr ha) (fun hb => Or.inl hb)

-- We just declared that a "theorem" but it is really a definition of a function!
-- Morally "theorem/lemma" is just a convenient syntax for "def". (we will see
-- some small subtlety later)

-- Tactic-mode proof (same result, different way to write it):
theorem or_comm_tactic (A B : Prop) : A ∨ B → B ∨ A := by
  intro h          -- assume h : A ∨ B
  cases h with     -- case analysis on h
  | inl ha => exact Or.inr ha   -- if A holds, produce B ∨ A via inr
  | inr hb => exact Or.inl hb   -- if B holds, produce B ∨ A via inl

-- Compare the two

#print or_comm_tactic


-- ============================================================
-- PART 2: NATURAL NUMBERS
-- ============================================================

/-
  Natural numbers are defined inductively in Lean's core library.
  Let's look at the definition:
-/

#print Nat
-- inductive Nat : Type where
--   | zero : Nat
--   | succ : Nat → Nat

-- The recursor (induction principle) generated automatically:
#check @Nat.rec
-- Nat.rec : {motive : Nat → Sort u} →
--           motive Nat.zero →
--           (∀ n, motive n → motive (Nat.succ n)) →
--           ∀ t : Nat, motive t

/-
  The recursor says: to define something for all natural numbers,
  give a value for zero (base case) and a way to go from n to succ n
  (inductive step). This is both recursion and induction in one!
-/

-- ============================================================
-- Pattern matching and the recursor
-- ============================================================

/-
  Pattern matching is syntactic sugar for the recursor.
  Let's see this in action:
-/

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ _ => false

-- Here is the same definition using the recursor explicitly:
def isZero_rec (n : Nat) : Bool :=
  @Nat.rec
    (fun _ => Bool)       -- motive: for any n, we produce a Bool
    true                  -- base case: isZero 0 = true
    (fun _ _ => false)    -- step: isZero (succ n) = false
    n


-- ============================================================
-- Defining addition
-- ============================================================

/-
  We define addition by recursion on the first argument.
  Note: Lean's built-in Nat.add recurses on the second argument,
  but we define our own to match the lecture.
-/

def add (n m : Nat) : Nat :=
  match n with
  | Nat.zero   => m                    -- equation (1)
  | Nat.succ n => Nat.succ (add n m)   -- equation (2)

-- We could attempt to print it, but Lean does not directly use the recursor in
-- a super-straightforward way.

-- Here a definition using the recursor explicitly:
def manual_add (n m : Nat) : Nat :=
  @Nat.rec
    (fun _ => Nat)                     -- motive: for any n, we produce a Nat
    m                                  -- base case: add 0 m = m
    (fun _ ih => Nat.succ ih)          -- step: add (succ n) m = succ (add n m)
    n


-- Let's verify our equations hold by computation:
#eval add 0 3
#eval add 2 1
#eval manual_add 3 4
-- What is the scam with these tests? The literals! There is magic happening here, transforming the arabic numerals into S(S(S(0))) and so on.
-- We might see how this kind of notations can be used and extended, and how they work in a future lecture.

-- These equalities hold by *definitional equality* (rfl):
example : add 0 3 = 3 := rfl -- One can wonder at this stage what is the meaning of the equal sign! Let's suspend the question for now.
example : add 2 1 = 3 := rfl

-- This also holds definitionally (equation 1):
example (m : Nat) : add 0 m = m := rfl

-- But this does NOT work with rfl (try uncommenting):
-- example (n : Nat) : add n 0 = n := rfl


-- ============================================================
-- PART 3: EQUALITY
-- ============================================================

-- ============================================================
-- Leibniz Equality
-- ============================================================

/-
  Leibniz equality: x and y are equal if every property of x
  is also a property of y.

  eqL x y := ∀ (P : S → Prop), P x → P y

  One can wonder, is it really a good definition of equality?
  For example it is not syntaxically obvious that it is symmetric.

  Let's see what properties it has, and how later how it relates to the
  equality actually defined and used by Lean.
-/

def eqL {S : Type} (x y : S) : Prop :=
  ∀ (P : S → Prop), P x → P y

notation:50 x " ≡ " y => eqL x y -- Notation, type \==  to write the symbol ≡

-- Reflexivity: x ≡ x
-- Proof: for any P, given P x, return P x (the identity function).
theorem eqL_refl {S : Type} (x : S) : x ≡ x :=
  λ_ => λh => h

-- It's just fun P h => h — the identity, as expected!

-- Symmetry: x ≡ y → y ≡ x
-- The trick: instantiate P with (fun z => z ≡ x).
theorem eqL_symm {S : Type} {x y : S} (e : x ≡ y) : y ≡ x :=
  e (fun z => z ≡ x) (eqL_refl x)


theorem eqL_congr_refl {S T : Type} {x : S} (f : S → T) (e : x ≡ x)
    : f x ≡ f x :=
    e (λz => eqL (f x) (f z))

-- Congruence: x ≡ y → f x ≡ f y
-- Instantiate P with (fun z => Q (f z)).
theorem eqL_congr {S T : Type} {x y : S} (f : S → T) (e : x ≡ y)
    : f x ≡ f y :=
    e (λz => eqL (f x) (f z))


-- Transitivity (exercise in the lecture, let's show it here):
theorem eqL_trans {S : Type} {x y z : S} (e1 : x ≡ y) (e2 : y ≡ z)
    : x ≡ z := by sorry




-- ============================================================
-- Inductive Equality (Lean's Eq)
-- ============================================================

/-
  Lean defines equality as an inductive type with one constructor: refl.
  That might seem seem strange at first, but it turns out to be equivalent to
  Leibniz equality, and a more convenient definition.  -/

#print Eq
-- inductive Eq {α : Sort u} (a : α) : α → Prop where
--   | refl : Eq a a

-- Advanced: Notice that 'a' is a parameter (fixed), the second argument is an index.
-- The only constructor is refl, which forces both arguments to be the same.

-- The eliminator:
#check @Eq.rec
-- Eq.rec : {α : Sort u} → {a : α} → {motive : α → Sort v} →
--          motive a → {b : α} → a = b → motive b
--  (to write an arrow → you can type \to)

-- This says: if P a holds and a = b, then P b holds.
-- It's essentially Leibniz equality (in reverse)!

-- ============================================================
-- Connecting Leibniz and Inductive Equality
-- ============================================================

-- Inductive => Leibniz:
-- Given a = b (inductive), we need ∀ P, P a → P b.
-- Eq.rec does exactly this.
theorem eq_to_eqL {S : Type} {x y : S} (e : x = y) : x ≡ y := by sorry



-- Leibniz => Inductive:
-- Given x ≡ y (i.e., ∀ P, P x → P y), we need x = y.
-- Instantiate P := fun z => x = z, and apply to rfl : x = x.
theorem eqL_to_eq {S : Type} {x y : S} (e : x ≡ y) : x = y := by sorry

-- simple!


-- ============================================================
-- PART 4: PROOF BY INDUCTION — add n 0 = n
-- ============================================================

/-
  We want to prove: ∀ n, add n 0 ≡ n.

  Since add recurses on the first argument:
  - add zero m =_{def} m            (equation 1)
  - add (succ n) m =_{def} succ (add n m)  (equation 2)

  For add n 0 ≡ n, we can't just compute — we need induction.
-/

-- Term-mode proof using the recursor directly:
theorem add_zero_term : ∀ n, add n 0 ≡ n := by sorry


theorem add_zero_term' : ∀ n, add n 0 ≡ n := by sorry




-- ============================================================
-- EXERCISES
-- ============================================================

/-
  Exercise 1 (warmup):
  - Prove transitivity of Leibniz equality amd prove equivalene of
  Leibniz and standard equality above.
  - Prove the two simple lemmas about adding zero above.
-/


/-
  Exercise 2: Derive symmetry and transitivity of Eq
  using no tactics.
-/


/-
  Exercise 3: add (succ n) m = succ (add n m)
-/

theorem add_succ_left (n m : Nat) : add (Nat.succ n) m = Nat.succ (add n m) := by sorry


/-
  Exercise 4: add n (succ m) = succ (add n m)
-/

theorem add_succ_right (n m : Nat) : add n (Nat.succ m) = Nat.succ (add n m) := by
  sorry

/-
  Exercise 5 (harder): Commutativity of addition.
  add n m = add m n
-/

theorem add_comm : ∀ n m, add n m = add m n := by
  sorry
