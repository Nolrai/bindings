def hello := "world"

inductive Lambda : Nat → Type u where
  | Var : Fin n → Lambda n
  | App : Lambda n → Lambda n → Lambda n
  | Abs : Lambda (n+1) → Lambda n

open Lambda

infix:70 "ᵛ" => λ n v => (Var v : Lambda n)

instance {n} : CoeFun (Lambda n) (λ _ => Lambda n → Lambda n) where
  coe := App

def ID : Lambda n → Lambda n := Abs $ (n+1)ᵛ0

theorem Eq.comm : a = b ↔ b = a :=
  ⟨Eq.symm, Eq.symm⟩

def beta_aux (arg : Lambda (n + depth)) (body : Lambda (n + depth + 1)) : Lambda (n + depth) :=
  match body with
  | Var v => 
    if v_lt : v.val < n 
      then by
        apply Var ∘ Fin.mk v.val
        apply Nat.lt_of_lt_of_le v_lt
        apply Nat.le_add_right
    else if v_eq : v = n
      then arg
      else
        have n_lt_v : n < v.val := by
          have ⟨v', vh⟩ := v
          clear body arg
          simp at *
          clear depth vh v
          apply Nat.lt_of_le_of_ne
          apply Nat.ge_of_not_lt
          exact v_lt
          rw [Eq.comm]
          exact v_eq 
        have h : v.val - 1 < n + depth := by
          suffices v.val - 1 + 1 < n + depth + 1 by
            apply Nat.lt_of_succ_lt_succ
            apply this
          rw [Nat.sub_add_cancel]
          exact v.isLt
          apply Nat.succ_le_of_lt
          apply Nat.lt_of_le_of_lt _ n_lt_v
          apply Nat.zero_le
        Var ⟨v.val - 1, h⟩
  | App l r => App (beta_aux arg l) (beta_aux arg r)
  | Abs newBody => 
    have newArg : Lambda (n + (depth + 1)) := by
      
    Abs (beta_aux newArg newBody)