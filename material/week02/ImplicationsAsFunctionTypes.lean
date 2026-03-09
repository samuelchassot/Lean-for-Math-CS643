variable (F G H a: Prop)

-- Represent the fact that F => G holds as having a function p: F -> G

-- a -> a is just the existence of identity function

theorem id: (a -> a) :=
  fun (x:a) => x         -- this is syntax for the identity on a

-- Modus ponens becomes just function application
theorem mp: (F -> G) -> F -> G :=
  fun (p: F -> G) =>
    fun (fHolds: F) =>
      p fHolds

-- The first axiom is a function that ignores its first argument (K combinator)

theorem wasAx1: F -> (G -> F) :=
  fun (F_holds: F) =>
    fun (G_holds: G) =>
      F_holds

-- The second axiom is S combinator
theorem wasAx2 :(F -> (G -> H)) -> (F -> G) -> (F -> H) :=
  fun (hyp1: (F -> (G -> H))) =>
    fun (hyp2: F -> G) =>
      fun (fHolds: F) =>
        hyp1 fHolds (hyp2 fHolds)

-- Another example theorem
theorem liftExample: (F -> G) -> (H -> F) -> (H -> G) :=
  fun (f_to_g: F -> G) =>
    fun (h_to_f: H -> F) =>
      fun (h: H) =>
        f_to_g (h_to_f h)

-- It may be hard to directly write such proof terms.
-- We can use interactive proof style where we move hypotheses
-- and establish local observations forward
theorem liftExampleHave:  (F -> G) -> (H -> F) -> (H -> G) := by
  intros f_to_g    -- turn LHS of an implication goal into an assumption
  intros h_to_f
  intros h         -- you can also write multiple things after intros
  have f := h_to_f h    -- we concluded that f holds
  have g := f_to_g f    -- so does g
  exact g               -- once we derive the goal, we can write `exact`

#print liftExampleHave
