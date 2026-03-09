theorem exAll {A:Type u} (P: A -> A -> Prop):
  (∃ u, ∀ v, P u v) -> (∀ x, ∃ y, P y x) := by
  intro h
  obtain ⟨ u1, Pu1 ⟩ := h
  intro x
  have Pu1x := Pu1 x
  exact ⟨ u1, Pu1x ⟩

theorem existImpl1 {A:Type u} (P: A -> Prop) (Q: Prop)
  (impl: ∀ x, (P x -> Q)):
  (∃ x, P x) -> Q := by
  intro h
  obtain ⟨ x, Px ⟩ := h
  have ha := impl x
  have hz := ha Px
  exact hz

theorem existImpl2 {A:Type u} (P: A -> Prop) (Q: Prop)
  (inner: (∃ x, P x) -> Q):
  ∀ x, (P x -> Q) := by
  intro a
  intro Pa
  exact inner ⟨ a, Pa ⟩


-- Homework

theorem total_refl {A:Type u} (P: A -> A -> Prop)
  (total: ∀ x y, P x y  ∨  P y x):
  ∀ x, P x x := by
  intro a
  have Pa := total a a
  cases Pa
  assumption
  assumption

theorem transitive_irr_anti {A: Type u} (less: A -> A -> Prop)
  (irr: ∀ x, ¬ less x x)
  (transitive: ∀ x y z, less x y -> less y z -> less x z):
  ∀ x y, (less x y ∨ x=y) -> (less y x ∨ y=x) -> x=y := by
  intro x
  intro y
  intros h1 h2
  cases h1 with
  | inl h1' =>


-- Property of pairs

#check Prod.fst
#eval Prod.fst (10, 20)
#check Prod.snd
#eval Prod.snd (10, 20)

theorem factorPairFun {A B C: Type u} (f_a: C -> A) (f_b: C -> B):
  ∃ f_ab: C -> (A × B), Prod.fst ∘ f_ab = f_a /\ Prod.snd ∘ f_ab = f_b := by
  sorry

theorem composeLemma {A B C: Type u} (f_a: C -> A) (f_b: C -> B) (f_ab: C -> (A × B))
  (h: Prod.fst ∘ f_ab = f_a /\ Prod.snd ∘ f_ab = f_b):
  ∀ c, f_ab c = (f_a c, f_b c) := by
  sorry

theorem factorPairFun1 {A B C: Type u} (f_a: C -> A) (f_b: C -> B)
  (f_ab1: C -> (A × B)) (factors1: Prod.fst ∘ f_ab1 = f_a /\ Prod.snd ∘ f_ab1 = f_b)
  (f_ab2: C -> (A × B)) (factors2: Prod.fst ∘ f_ab2 = f_a /\ Prod.snd ∘ f_ab2 = f_b):
  f_ab1 = f_ab2 := by
  sorry

-- Property of sums

#check Nat ⊕ Nat
#check Sum.inl
#check Sum.inr

#print Sum.elim

theorem sum_elim_defA {A B C: Type u} (f_a: A -> C) (f_b: B -> C) (a: A):
  Sum.elim f_a f_b (Sum.inl a) = f_a a    := by sorry

theorem sum_elim_defB {A B C: Type u} (f_a: A -> C) (f_b: B -> C) (b: B):
  Sum.elim f_a f_b (Sum.inr b) = f_b b    := by sorry

theorem factorSumFunA {A B C: Type u} (f_a: A -> C) (f_b: B -> C):
  (Sum.elim f_a f_b) ∘ Sum.inl = f_a := by sorry

theorem factorSumFunB {A B C: Type u} (f_a: A -> C) (f_b: B -> C):
  (Sum.elim f_a f_b) ∘ Sum.inr = f_b := by sorry

theorem factorSumFun {A B C: Type u} (f_a: A -> C) (f_b: B -> C):
  ∃ f_ab: A ⊕ B -> C, f_ab ∘ Sum.inl = f_a /\ f_ab ∘ Sum.inr = f_b := by
  sorry

theorem composeLemmaDual {A B C: Type u} (f_a: A -> C) (f_b: B -> C) (f_ab: (A ⊕ B) -> C)
  (h: f_ab ∘ Sum.inl = f_a /\ f_ab ∘ Sum.inr = f_b):
  f_ab = Sum.elim f_a f_b := by
  sorry

-- Drinker's paradox

#check Classical.byContradiction

theorem drinker {A:Type u} (a1:A) (Q: A -> Prop): -- a1 witnesses A != ∅
  ∃ d, (Q d -> ∀ x, Q x) := by
  sorry
