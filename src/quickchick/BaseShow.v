From QuickChick Require Import QuickChick.
Require Import String. Open Scope string.

Require Import Base.

Instance show_𝔗 : Show 𝔗 :=
  {| show :=
      let fix aux T :=
      match T with
      | Unit => "Unit"
      | Void => "Void"
      | 𝔗mult T1 T2 => aux T1 ++ " × " ++ aux T2
      | 𝔗plus T1 T2 => aux T1 ++ " + " ++ aux T2
      | 𝔗impl T1 T2 => aux T1 ++ " → " ++ aux T2
      | 𝔗ceil A => "⌈-⌉"
      end
      in aux
  |}.


Instance show_𝔄 : Show 𝔄 :=
  {| show :=
      let fix aux A :=
      match A with
      | 𝔄1 => "1"
      | 𝔄0 => "0"
      | 𝔄mult A1 A2 => aux A1 ++ " ⊗ " ++ aux A2 
      | 𝔄plus A1 A2 => aux A1 ++ " ⊕ " ++ aux A2
      | 𝔄impl A1 A2 => aux A2 ++ " ⊸ " ++ aux A2
      | 𝔄flor T => "⌊-⌋"
      | 𝔄diam A1 => "◇" ++ aux A1
      end
      in aux
  |}.

Instance show_𝔱 : Show 𝔱 :=
  {| show :=
      let fix aux t :=
      match t with
      | 𝔱id _ => "x"
      | 𝔱hole => "()"
      | 𝔱holecase t1 => "case " ++ aux t1 ++ " of ()"
      | 𝔱pair t1 t2 => "(" ++ aux t1 ++ ", " ++ aux t2 ++ ")"
      | 𝔱prj 1 t1 => "π₁ " ++ aux t1
      | 𝔱prj _ t1 => "π₂ " ++ aux t1
      | 𝔱inj 1 t1 => "in₁ " ++ aux t1
      | 𝔱inj _ t1 => "in₂ " ++ aux t1
      | 𝔱case t' x1 t1 x2 t2 => "case " ++ aux t' ++ "(in₁ x₁ → " ++ aux t1 ++ " | in₂ x₂ → " ++ aux t2 ++ ")"
      | 𝔱lambda x t1 => "λx. " ++ aux t1
      | 𝔱app t1 t2 => aux t1 ++ " " ++ aux t2
      | 𝔱suspend e => "suspend -"
      end
      in aux
  |}.

Instance show_𝔢 : Show 𝔢 :=
  {| show :=
      let fix aux e :=
      match e with
      | 𝔢id _ => "x"
      | 𝔢hole => "()"
      | 𝔢holecase e1 => "case " ++ aux e1 ++ " of ()"
      | 𝔢holelet e1 e2 => "let () = " ++ aux e1 ++ " in " ++ aux e2
      | 𝔢pair e1 e2 => "(" ++ aux e1 ++ ", " ++ aux e2 ++ ")"
      | 𝔢let x1 x2 e1 e2 => "let (x₁, x₂) = " ++ aux e1 ++ " in " ++ aux e1
      | 𝔢inj 1 e1 => "in₁ " ++ aux e1
      | 𝔢inj _ e1 => "in₂ " ++ aux e1
      | 𝔢case e' x1 e1 x2 e2 => "case " ++ aux e' ++ "(in₁ x₁ → " ++ aux e1 ++ " | in₂ x₂ → " ++ aux e2 ++ ")"
      | 𝔢lambda x e1 => "λx. " ++ aux e1
      | 𝔢app e1 e2 => aux e1 ++ " " ++ aux e2
      | 𝔢return e1 => "return " ++ aux e1
      | 𝔢bind x e1 e2 => "bind x = " ++ aux e1 ++ " in " ++ aux e2
      | 𝔢force t => "force -"
      | 𝔢flor t => "⌊-⌋"
      | 𝔢florlet x e1 e2 => "let ⌊x⌋ = " ++ aux e1 ++ " in " ++ aux e2
      end
      in aux
  |}.
