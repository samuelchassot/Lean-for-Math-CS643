-- To illustrate formal proof systems, we use minimal propositional logic
-- You should first do this part on whiteboard, only then in Lean.

-- You can try this file in https://live.lean-lang.org/
-- or vscode with this extension:
--    https://marketplace.visualstudio.com/items?itemName=leanprover.lean4

-- The only operator is implication written using equality and greater than
opaque Imp : Prop → Prop → Prop
infixr:25 " ⟹ " => Imp

-- The only inference rule is modus ponens: from F => G and F infer G.
--     F=>G   F
--     ---------
--        G
axiom mp {F G : Prop} : (F ⟹ G) → F → G
-- (We used Lean's implication/function constructor for inference.)

-- 1st axiom schema: for every two propositions F,G we have axiom F=>(G=>F)
axiom ax1 : ∀ F G : Prop,
            F ⟹ (G ⟹ F)

-- 2nd axiom schema: for every three propositions F,G,H we have the axiom below.
-- (Think why this is always true in classical propositional logic.)
axiom ax2 : ∀ F G H : Prop,
           (F ⟹ (G ⟹ H)) ⟹ ((F ⟹ G) ⟹ (F ⟹ H))

-- unless otherwise stated, a is some arbitrary proposition
variable (a : Prop)

-- We show how to derive a proof of a=>a from two axioms above
theorem a_implies_a_hard: a ⟹ a := by
  have h1 : a ⟹ ((a ⟹ a) ⟹ a) := ax1 a (a ⟹ a)
  have h2 : a ⟹ (a ⟹ a)       := ax1 a a
  have h3 : (a ⟹ ((a ⟹ a) ⟹ a)) ⟹ ((a ⟹ (a ⟹ a)) ⟹ (a ⟹ a)) := ax2 a (a ⟹ a) a
  have h4 : (a ⟹ (a ⟹ a)) ⟹ (a ⟹ a) := mp h3 h1
  have h5 : a ⟹ a                   := mp h4 h2
  exact h5
