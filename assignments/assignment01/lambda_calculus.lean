namespace LambdaAssignment

-- Lambda calculus is important for proof assistants such as Lean
-- as well as for functional programming in general.

-- Functions defined by `def` in Lean are terminating and total functions
-- that have types for arguments and results.

-- This function computes a square of a natural number given as an argument.
def squareOf (x:Nat): Nat :=
  x * x

-- `Nat` denotes natural numbers.
-- Multiplication is `*`

-- We can evaluate expressions using functions we defined.
-- Instead of `squareOf(5)` we simply write `squareOf 5`

#eval squareOf 5

-- The key construct of λ calculus is an anonymous function.
-- If we want to refer to the squaring function without using a name,
-- we can denote it in mathematics using `x ↦ x*x`. In Lean,
-- we write this as `λx => x*x`

def square: Nat -> Nat :=
  λx:Nat => x * x

-- We can prove these two functions are the same using `rfl`,
-- because Lean represents squareOf and square using the same expression.

theorem sameSquare: (squareOf = square) := rfl
--      ----------  -------------------   ------
--        name    :   statement        := proof

-- Here `rfl` is the reflexivity of equality saying a=a

#check rfl

/- λ gives us a notation for solving equations, such as
          square x = x*x
   for the meaning of `square`, here:
          square = (λ x => x*x)

   The key rule for λ calculus is that we can apply
     function to its argument, so, for example,

      (λx => x*x)(x+1) = (x+1)*(x+1)

   This rule is called β-reduction.
-/

theorem betaExample: square (x+1) = (x+1)*(x+1) := rfl

-- Lean can infer the type of the argument(s) after lambda
def square_v2: Nat -> Nat :=
  λx => x * x

-- We can use `fun ` instead of λ, if you prefer
def square_v3: Nat -> Nat :=
  fun x => x * x

-- We can rename the bound variable(s); the function stays the same.
-- This is called α-renaming
theorem alphaExample: ((λ x:Nat => x*x) = (λ y:Nat => y*y)) := rfl

-- A final rule is eta extensionality: we can cancel applications and lambdas as follows:
theorem eta:   ((λ x:Nat => f x) = f) :=
  rfl

-- Here is successor using built-in natural numbers.

def plusOne: Nat -> Nat :=
  λx => x + 1

-- Multiple arguments: represent them as functions returning functions
def plus: Nat -> Nat -> Nat :=
  λx => λy => x+y

-- When we write plus x y, it means ((plus x) y)
#eval plus 5 3 == (plus 5) 3

-- We can choose to give only one argument and get back a function
def plusOne_v2: Nat -> Nat := plus 1

theorem plusOneExample: (plusOne = λ x => 1 + x /- TODO: write a lambda here -/) := by
  unfold plusOne
  funext x
  induction x
  · rfl
  · rw [Nat.add_succ]
    simp
    rw [Nat.add_comm]

-- Aside: if we wrote 1+x above, we would need the proof more complex than `rfl`:

theorem plusOneSwapped: (plusOne = (λ x:Nat => 1+x)) := by
  unfold plusOne     -- expand the function definition
  funext x           -- to prove functions equal, prove them for arbitrary argument
  rw [Nat.add_comm]  -- commutativity for addition on Nat from the library

-- Composing functions. Here a,b,c are types for domains and codomains.
-- We wrote them inside {a b c}, which means Lean will infer them when we use compose.

def compose {a b c} (f: a -> b) (g: b -> c): a -> c :=
  λ x => g (f x)


def sq1 := compose square plusOne
def p1sq := compose plusOne square

#eval sq1 3 == 10
#eval p1sq 3 == 16

-- Now, define n^4 using the functions above so that the theorem passes
def power4: Nat -> Nat :=
  compose square square

-- #eval power4 3 == 81

theorem power4is: power4 x = (x*x)*(x*x) := by
  unfold power4
  unfold square
  unfold compose
  rfl

/- In higher-order logic, equality can be used to express quantifiers.
   Suppose p is a property. Saying p is always true for all possible arguments means it is equivalent to a constant true function.
-/

def constantTrue : Nat -> Prop :=
  λ _ => True

theorem encodingForall (p: Nat -> Prop): (∀ x, p x) <-> (p = constantTrue) := by
  -- We will understand such proofs later; there may be better ways to write them, too.
  constructor
  · intro hAll     -- -> direction. hAll is (∀ x, p x)
    funext x       -- let x be arbitrary
    apply propext  -- to prove equality on Prop, prove again equivalence
    constructor
    · intro _           -- first direction: prove constTrue x
      trivial           -- evaluate constTrue on anything
    · intro _           -- second direction: prove p x
      exact hAll x      -- instantiate the hypothesis
  · intro hEq      -- <- direction. hEq is p=constantTrue
    intro x        -- let x be arbitrary
    rw [hEq]       -- rewrite the goal to True
    trivial

end LambdaAssignment

namespace ChurchNumerals

-- We encode a number k as a function that composes its argument function k times.
-- Given an arbitrary type a, numeral takes a function a -> a
-- it iterates it k times to get a repeated function of same type a -> a

-- This is a shorthand for numeral whose functions work on some type a
def numeral a :=
  (a -> a) -> (a -> a)

def one {a}: numeral a :=
  λf => λv => f v

def zero {a}: numeral a :=
  λ f => f

def plus {a} (x: numeral a) (y: numeral a): numeral a :=
  λ f: a -> a => λ v =>
    x f (y f v)

def two {a}: numeral a := plus one one
def three {a}: numeral a := plus two one
def four {a}: numeral a := plus two two

def times {a} (x: numeral a) (y: numeral a): numeral a :=
  λ f: a -> a => λ v =>
    x (y f) v


theorem mulOne {a} (x: numeral a): (times one x = x) := by
  unfold times
  unfold one
  funext f
  simp

theorem oneMul {a} (x: numeral a): (times x one = x) := by
  unfold times
  funext f
  constructor

def fromNumeral (x: numeral String): String :=
  x (fun (s: String) => s.append "i") ""


#eval fromNumeral (plus four two)

/- Food for thought:
   can you similarly define a power function on church numerals,
   computing x^n
-/

end ChurchNumerals
