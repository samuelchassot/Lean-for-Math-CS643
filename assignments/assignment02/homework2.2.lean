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
    cases h2 with
    | inl h2' =>
      have invalid := transitive x y x
      have invalid' := (invalid h1') h2'
      simp [irr] at invalid'
    | inr h2' =>
      simp [h2']
  | inr h1' =>
    simp [h1']


-- Property of pairs

#check Prod.fst
#eval Prod.fst (10, 20)
#check Prod.snd
#eval Prod.snd (10, 20)

theorem factorPairFun {A B C: Type u} (f_a: C -> A) (f_b: C -> B):
  ∃ f_ab: C -> (A × B), Prod.fst ∘ f_ab = f_a /\ Prod.snd ∘ f_ab = f_b := by
  exists (fun c => (f_a c, f_b c))

theorem composeLemma {A B C: Type u} (f_a: C -> A) (f_b: C -> B) (f_ab: C -> (A × B))
  (h: Prod.fst ∘ f_ab = f_a /\ Prod.snd ∘ f_ab = f_b):
  ∀ c, f_ab c = (f_a c, f_b c) := by
  intro c
  rcases h with ⟨hA, hB⟩
  rw [←hA, ←hB]
  simp


theorem factorPairFun1 {A B C: Type u} (f_a: C -> A) (f_b: C -> B)
  (f_ab1: C -> (A × B)) (factors1: Prod.fst ∘ f_ab1 = f_a /\ Prod.snd ∘ f_ab1 = f_b)
  (f_ab2: C -> (A × B)) (factors2: Prod.fst ∘ f_ab2 = f_a /\ Prod.snd ∘ f_ab2 = f_b):
  f_ab1 = f_ab2 := by
  rcases factors1 with ⟨h11, h12⟩
  rcases factors2 with ⟨h21, h22⟩
  funext c
  apply Prod.ext
  · have  h11c := congrFun h11 c
    simp at h11c
    have h21c := congrFun h21 c
    simp at h21c
    rw [h11c, h21c]
  · have  h12c := congrFun h12 c
    simp at h12c
    have h22c := congrFun h22 c
    simp at h22c
    rw [h12c, h22c]

-- Property of sums

#check Nat ⊕ Nat
#check Sum.inl
#check Sum.inr

#print Sum.elim

theorem sum_elim_defA {A B C: Type u} (f_a: A -> C) (f_b: B -> C) (a: A):
  Sum.elim f_a f_b (Sum.inl a) = f_a a    := by
  simp

theorem sum_elim_defB {A B C: Type u} (f_a: A -> C) (f_b: B -> C) (b: B):
  Sum.elim f_a f_b (Sum.inr b) = f_b b    := by
  simp

theorem factorSumFunA {A B C: Type u} (f_a: A -> C) (f_b: B -> C):
  (Sum.elim f_a f_b) ∘ Sum.inl = f_a := by
  simp

theorem factorSumFunB {A B C: Type u} (f_a: A -> C) (f_b: B -> C):
  (Sum.elim f_a f_b) ∘ Sum.inr = f_b := by
  simp

theorem factorSumFun {A B C: Type u} (f_a: A -> C) (f_b: B -> C):
  ∃ f_ab: A ⊕ B -> C, f_ab ∘ Sum.inl = f_a /\ f_ab ∘ Sum.inr = f_b := by
  exists (Sum.elim f_a f_b)

theorem composeLemmaDual {A B C: Type u} (f_a: A -> C) (f_b: B -> C) (f_ab: (A ⊕ B) -> C)
  (h: f_ab ∘ Sum.inl = f_a /\ f_ab ∘ Sum.inr = f_b):
  f_ab = Sum.elim f_a f_b := by
  funext x
  rcases h with ⟨hA, hB⟩
  cases x with
    | inl a =>
      simp
      have hAA := congrFun hA a
      assumption
    | inr b =>
      simp
      have hBB := congrFun hB b
      assumption

-- Drinker's paradox

#check Classical.byContradiction

theorem drinker {A:Type u} (a1:A) (Q: A -> Prop): -- a1 witnesses A != ∅
  ∃ d, (Q d -> ∀ x, Q x) := by
  by_cases h : ∀ x : A, Q x
  · exists a1
    intro h2
    assumption
  · have hex : ∃ d : A, ¬ Q d := by
      apply Classical.byContradiction
      intro hne
      apply h
      intro x
      apply Classical.byContradiction
      intro hx
      apply hne
      exact ⟨x, hx⟩
    obtain ⟨x, Px⟩ := hex
    exists x
    intro Pxx
    contradiction
