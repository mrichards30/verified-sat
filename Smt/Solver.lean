import Lean.Parser
open Lean
open Lean.Parser

inductive PropLogicExpr where
  | True : PropLogicExpr
  | Var : String -> PropLogicExpr
  | And : PropLogicExpr -> PropLogicExpr -> PropLogicExpr
  | Not : PropLogicExpr -> PropLogicExpr

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

theorem substAll_rec : substAll e ((k, v) :: xs) = subst (substAll e xs) k v := by
  induction xs with
    | nil => rfl
    | cons y ys ih => sorry

theorem subst_not : substAll (.Not e) vs = .Not (substAll e vs) := by
  induction e with
  | True =>
    induction vs with
      | nil => rfl
      | cons x xs ih =>
        have p : hasVars (.Not .True) = false := rfl
        have q : hasVars .True = false := rfl
        simp [p, substAll_const, q]
  | Var n =>
    have p : hasVars (.Not (.Var n)) = true := rfl
    induction vs with
      | nil => rfl
      | cons x xs ih => sorry
  | Not e1 ih => sorry
  | And e1 e2 ih1 ih2 => sorry

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
    | .And .True .True => .True
    | .And _ (.Not .True) => .Not .True
    | .And (.Not .True) _ => .Not .True
    | .And e1 e2 => .And e1 e2
    | .Not e1 => .Not e1
    | .Var n => .Var n

#eval solve $ .And (.Var "test") (.Not (.Not $ .Var "test"))

theorem solve_correct_some :
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
    sorry

theorem simplifySplit :
  simplifyExpr (substAll (.And e1 e2) solns) = .True <-> (simplifyExpr (substAll e1 solns) = .True ∧ simplifyExpr (substAll e2 solns) = .True)
    := sorry

theorem subst_soln_var_isSome : ∀n, ∃solns, simplifyExpr (substAll (.Var n) solns) = .True := by
  intro n
  exists [(n, true)]
  simp [subst_one, subst, mkBool, simplifyExpr]

theorem solve_correct_none
  : ¬(∃solns, simplifyExpr (substAll expr solns) = .True) -> solve expr = none := by
  induction expr with
  | True =>
    intro p
    have q : hasVars .True = false := rfl
    have r : ∃solns, substAll .True solns = .True := by simp [q, substAll_const]
    have s : ∃solns, simplifyExpr (substAll .True solns) = .True := sorry
    contradiction
  | Var n =>
    intro p
    have p' : ∃solns, simplifyExpr (substAll (.Var n) solns) = .True := by
      simp [subst_soln_var_isSome]
    contradiction
  | Not e ih =>
    intro p
    simp [solve, solveFor]
    sorry
  | And e1 e2 ih1 ih2 =>
    intro p
    simp [solve, solveFor]
    simp [simplifySplit] at p
    cases h1 : Classical.em $ ∃x, simplifyExpr (substAll e1 x) = .True with
      | inl q => (
          cases h2 : Classical.em $ ∃x, simplifyExpr (substAll e2 x) = .True with
            | inl r => sorry
            | inr r =>
              simp [r, solve] at ih2
              rw [ih2]
              simp [merge]
          )
      | inr q =>
        simp [q, solve] at ih1
        rw [ih1]
        simp [merge]

theorem solve_correctness :
  (¬∃solns, simplifyExpr (substAll expr solns) = .True) -> solve expr = none
  ∧ (∀solns, solve expr = some solns -> simplifyExpr (substAll expr solns) = .True) := by
  sorry
