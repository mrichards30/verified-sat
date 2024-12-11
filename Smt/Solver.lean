inductive PropLogicExpr where
  | True : PropLogicExpr
  | Var : String -> PropLogicExpr
  | And : PropLogicExpr -> PropLogicExpr -> PropLogicExpr
  | Not : PropLogicExpr -> PropLogicExpr
deriving BEq

def mkBool (b : Bool) : PropLogicExpr :=
  match b with
    | true => .True
    | false => .Not .True

def subst (expr : PropLogicExpr) (var : String) (val : Bool) : PropLogicExpr :=
  match expr with
    | .True => expr
    | .Not e1 => .Not $ subst e1 var val
    | .And e1 e2 => .And (subst e1 var val) (subst e2 var val)
    | .Var n => if n == var then mkBool val else expr

def substAll : PropLogicExpr -> List (String × Bool) -> PropLogicExpr :=
  List.foldl $ Function.uncurry ∘ subst

def hasVars : PropLogicExpr -> Bool
  | .True => false
  | .Var _ => true
  | .Not e => hasVars e
  | .And e1 e2 => hasVars e1 || hasVars e2

theorem subst_nil : substAll expr [] = expr := rfl
theorem subst_one : substAll expr [(k, v)] = subst expr k v := rfl
theorem substAll_cons : substAll e ((k, v)::xs) = substAll (subst e k v) xs := rfl

theorem subst_const : hasVars expr = false -> subst expr k v = expr := by
  induction expr with
  | True => simp [subst]
  | Var n =>
    have p : hasVars (.Var n) = true := rfl
    intro q
    contradiction
  | Not e ih =>
    simp [hasVars, subst]
    exact ih
  | And e1 e2 ih1 ih2 =>
    simp [hasVars, subst]
    intros p q
    simp [ih1 p, ih2 q]

theorem substAll_const : hasVars expr = false -> substAll expr vs = expr := by
  intro p
  induction vs with
  | nil => rfl
  | cons x xs ih =>
    rw [substAll_cons, subst_const, ih]
    exact p

private def merge : Option (List (String × Bool)) -> Option (List (String × Bool)) -> Option (List (String × Bool))
  | some [], some ys => some ys
  | some ((n, b) :: xs), some ys =>
      match List.lookup n ys with
      | some b' => if b = b' then merge xs ys else none
      | none => merge xs $ (n, b)::ys
  | _, _ => none

def solveFor (target : Bool) (expr : PropLogicExpr) : Option (List (String × Bool)) :=
  match expr with
    | .True => if target then some [] else none
    | .Not e1 => solveFor (!target) e1
    | .And e1 e2 => merge (solveFor true e1) (solveFor true e2)
    | .Var n => some $ [(n, target)]

def solve : (expr : PropLogicExpr) -> Option (List (String × Bool)) := solveFor true

def simplifyExpr (expr : PropLogicExpr) : PropLogicExpr :=
  match expr with
    | .True => .True
    | .Var n => .Var n
    | .Not e1 => (
      match simplifyExpr e1 with
        | .Not e2 => e2
        | e2 => .Not e2
    )
    | .And e1 e2 => (
      match (simplifyExpr e1, simplifyExpr e2) with
        | (.True, e2') => e2'
        | (e1', .True) => e1'
        | (.Not .True, _) => .Not .True
        | (_, .Not .True) => .Not .True
        | (e1', e2') =>
          if e1' == e2' then e1'
          else if e1' == .Not e2' || .Not e1' == e2' then .Not .True
          else .And e1' e2'
    )

#eval simplifyExpr $ (PropLogicExpr.Var "n").And (.Not .True)
#eval simplifyExpr $ .Not ((PropLogicExpr.Var "n").And (.Not (.Var "n")))
#eval simplifyExpr $ .And (.And (.Not .True) .True) (.And (.Not .True) (.Not .True))

def isNeg (e : PropLogicExpr) := ∃e', e = .Not e'

theorem simplifyMinimises : ¬hasVars e -> (simplifyExpr e = .True ∨ simplifyExpr e = .Not .True) := by
  induction e with
    | True => simp [simplifyExpr]
    | Var n => simp [simplifyExpr, hasVars]
    | Not e ih =>
      intro const
      have p : ¬hasVars e := sorry
      specialize ih p
      cases ih with
        | inl h =>
          have h' : simplifyExpr e = .True -> simplifyExpr (.Not e) = .Not .True := by
            cases Classical.em $ isNeg e with
              | inl is_neg =>
                obtain ⟨e1, eh⟩ := is_neg
                rw [eh]
                intro not_e1_eq_true
                have not_not_def : simplifyExpr e1.Not.Not = simplifyExpr e1 := sorry
                rw [not_not_def]
                sorry
              | inr is_not_neg =>
                simp [h]
                have f : simplifyExpr (.Not e) = .Not (simplifyExpr e) := sorry
                simp [f, h]
          rw [h']
          simp
          exact h
        | inr => sorry

    | And e1 e2 ih1 ih2 => sorry

#eval solve $ .And (.Var "test") (.Not (.Not $ .Var "test"))

theorem simplifyDistrib_and : simplifyExpr (.And e1 e2) = simplifyExpr (.And (simplifyExpr e1) (simplifyExpr e2)) := sorry

theorem simplifyAnd (e1 e2 : PropLogicExpr) :
  simplifyExpr (e1.And e2) = PropLogicExpr.True -> simplifyExpr e1 = .True ∧ simplifyExpr e2 = .True := by
  intro p
  cases Classical.em $ simplifyExpr e1 = PropLogicExpr.True ∧ simplifyExpr e2 = PropLogicExpr.True with
    | inl q =>
      exact q
    | inr q =>
      have q' : ¬simplifyExpr e1 = PropLogicExpr.True ∨ ¬simplifyExpr e2 = PropLogicExpr.True := sorry
      cases q' with
       | inl q1 => sorry
       | inr q1 => sorry


theorem distribSubst_and : simplifyExpr (substAll (.And e1 e2) solns) = simplifyExpr (.And (substAll e1 solns) (substAll e2 solns)) := sorry

theorem solutionSplitIff :
  (∀solns, simplifyExpr (substAll (.And e1 e2) solns) = .True
  <-> (simplifyExpr (substAll e1 solns) = .True ∧ simplifyExpr (substAll e2 solns) = .True)) := by
  intro solns
  apply Iff.intro
  intro prem
  rw [distribSubst_and] at prem
  exact simplifyAnd (substAll e1 solns) (substAll e2 solns) $ prem

  intro prem
  rcases prem with ⟨p, q⟩
  induction solns with
    | nil =>
      simp_all [subst_nil]
      rw [simplifyDistrib_and]
      simp [p, q]
      rfl
    | cons x xs ih =>
      rw [substAll_cons] at p
      sorry

theorem subst_soln_var_isSome : ∀n, ∃solns, simplifyExpr (substAll (.Var n) solns) = .True := by
  intro n
  exists [(n, true)]
  simp [subst_one, subst, mkBool, simplifyExpr]

theorem solveFor_not_none : -- maybe pointless
  ¬(∃solns, simplifyExpr (substAll (.Not e) solns) = mkBool target) -> solveFor target (.Not e) = none := by
  induction e with
  | True =>
    intro solns
    have false_const : ¬(hasVars PropLogicExpr.True.Not) := by simp [hasVars]
    simp [false_const, substAll_const, simplifyExpr] at solns
    cases target with
    | true => simp [solveFor]
    | false => contradiction
  | Var n => sorry
  | Not e1 ih => sorry
  | And e1 e2 ih1 ih2 => sorry

theorem solveValidSub :
  ∀solns, solve expr = some solns -> simplifyExpr (substAll expr solns) = .True := by
  induction expr with
  | True =>
    simp [solve, solveFor]
    simp [subst_nil, simplifyExpr]
  | Var n =>
    simp [solve, solveFor, subst_one, subst, mkBool, simplifyExpr]
  | Not e1 ih =>
    simp [solve, solveFor]
    sorry
  | And e1 e2 ih1 ih2 =>
    simp [solve, solveFor]
    intros solns p
    simp [solutionSplitIff]
    have test := ih1 solns
    sorry

-- iff P has no solutions to make P true, then ¬P
-- has no solutions to make ¬P false.
theorem solveFor_not_target :
  solveFor target e = none <-> solveFor (¬target) (.Not e) = none := sorry

theorem solveNilImpConst : solveFor target e = some [] -> ¬hasVars e := by
  induction e with
  | True => cases target <;> simp [solve, solveFor, hasVars]
  | Var n => simp [solve, solveFor, hasVars]
  | And e1 e2 ih1 ih2 => sorry
  | Not e ih => sorry

theorem solveIffSub
  : (∃solns, simplifyExpr (substAll expr solns) = .True) <-> Option.isSome (solve expr) := by
  induction expr with
  | True =>
    apply Iff.intro
    intro p
    have q : hasVars .True = false := rfl
    have r : ∃solns, substAll .True solns = .True := by simp [q, substAll_const]
    have s : ∃solns, simplifyExpr (substAll .True solns) = .True := sorry
    simp [solve, solveFor]
    have q : hasVars .True = false := rfl
    simp [solve, solveFor, q, substAll_const, simplifyExpr]
  | Var n =>
    apply Iff.intro
    intro p
    simp [solve, solveFor]
    simp [subst_soln_var_isSome]
  | Not e ih =>
    apply Iff.intro
    intro p
    simp [solve, solveFor]
    -- simplifyExpr (substAll e.Not solns) = .True <-> simplifyExpr (.Not (substAll e solns)) = .True
    -- ... <-> simplifyExpr (.Not (substAll e solns)) = .True
    sorry
    sorry
  | And e1 e2 ih1 ih2 =>
    apply Iff.intro
    intro p
    simp [solve, solveFor]
    cases Classical.em $ ∃solns, simplifyExpr (substAll e1 solns) = PropLogicExpr.True with
      | inl q =>
        cases Classical.em $ ∃solns', simplifyExpr (substAll e2 solns') = PropLogicExpr.True with
          | inl r =>
            rw [merge]
            -- intros xs e1Nil e2Some
            -- simp [solveNilImpConst] at e1Nil
            sorry
            sorry
            sorry
          | inr r =>
            rw [merge]
            -- intros a b c
            -- simp [r, solve] at ih2
            -- rw [ih2] at c
            -- contradiction
            -- intro n b c ys zz zy
            -- simp [r, solve] at ih2
            -- rw [zy] at ih2
            -- contradiction
            sorry
            sorry
            sorry
      | inr q =>
        simp [q, solve] at ih1
        simp [ih1, merge]
        sorry
    sorry

-- `solve` only returns a solution when there exists a valid set of substitutions to solve
-- the equation, and the solution that `solve` returns is one of these valid sets.
theorem solveCorrect :
  ((∃solns, simplifyExpr (substAll expr solns) = .True) <-> Option.isSome (solve expr))
  ∧ (∀solns, solve expr = some solns -> simplifyExpr (substAll expr solns) = .True) :=
  And.intro solveIffSub solveValidSub
